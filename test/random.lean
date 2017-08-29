
import system.io
import data.bitvec
import data.stream
import util.data.list

open list io applicative

structure generator :=
  (seed1 : bitvec 32)
  (seed2 : bitvec 32)

namespace generator

/-- ported from
    https://hackage.haskell.org/package/random
    -/

def from_nat32 (s : bitvec 32) : generator :=
let s₀ := s.to_nat,
    s₁ := bitvec.of_nat 32 $ s₀ % 2147483562,
    q  := s₀ / 2147483562,
    s₂ := bitvec.of_nat 32 $ q % 2147483398 in
⟨ s₁ + 1, s₂ + 1 ⟩

def next : generator → bitvec 31 × generator
  | ⟨ s1, s2 ⟩ :=
let k := s1.to_int / 53668,
    s1'  := 40014 * (s1.to_int - k * 53668) - k * 12211,
    s1'' := if s1' < 0 then s1' + 2147483563 else s1',

    k'   := s2.to_int / 52774,
    s2'  := 40692 * (s2.to_int - k' * 52774) - k' * 3791,
    s2'' := if s2' < 0 then s2' + 2147483399 else s2',
    z    := s1'' - s2'',
    z'   := if z < 1 then z + 2147483562 else z
in ⟨ (bitvec.of_int _ z').tail, (bitvec.of_int _ s1'').tail, (bitvec.of_int _ s2'').tail ⟩


def split : generator → generator × generator
 | ⟨ s1, s2 ⟩ :=
let    nx := (next ⟨s1,s2⟩).2,
       ⟨t1,t2⟩ := nx,
       new_s1 := if s1 = 2147483562
                 then  1
                 else s1 + 1,

       new_s2 := if s2 = 1
                 then 2147483398
                 else s2 - 1,

       -- no statistical foundation for this!
       left  : generator := ⟨new_s1, t2⟩,
       right : generator := ⟨t1, new_s2⟩
in ⟨ left, right ⟩

end generator

universes u

namespace tactic.interactive

open tactic
open lean.parser
open interactive
open interactive.types

meta def time_in_nanos : tactic ℕ :=
do time ← tactic.run_io (λ [ioi : io.interface],
          @io.cmd ioi { cmd := "gdate", args := [ "+%s%N" ] } ),
   pure time.to_nat

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def unfold_local (n : parse ident) : tactic unit := do
e ← resolve_name n >>= to_expr,
g ← target,
t ← infer_type e,
v ← mk_meta_var t,
h ← to_expr ``(%%e = (%%v : %%t)) >>= assert `h,
solve1 (do
  tactic.revert e,
  g ← target,
  match g with
   | (expr.elet n _ e b) := tactic.change (expr.instantiate_local n e b)
   | _ := fail $ to_string n ++ " is not a local definition"
  end,
  tactic.intros, refl ),
rewrite_target h,
tactic.clear h

meta def funext1 (x : parse ident_ ?) : tactic unit := do
`[apply funext],
intro x

meta def funext : parse ident_ * → tactic unit
 | [] := return ()
 | (x :: xs) := funext1 x >> funext xs

end tactic.interactive

def rand (α : Type u) := generator → α × generator

namespace rand

variables {α β γ : Type u}

protected def pure (x : α) : rand α :=
λ g, (x,g)

protected def bind (x : rand α) (f : α → rand β) : rand β :=
λ g,
let r := x g in
f r.1 r.2

instance : has_bind rand :=
⟨ @rand.bind ⟩

instance : has_pure rand :=
⟨ @rand.pure ⟩

lemma bind_assoc (x : rand α) (f : α → rand β) (g : β → rand γ)
: x >>= f >>= g = x >>= (λ i, f i >>= g) :=
begin
  funext sz,
  simp [has_bind.bind,rand.bind],
end

lemma pure_bind (x : α) (f : α → rand β)
: pure x >>= f = f x :=
by refl

lemma id_map (x : rand α)
: x >>= pure ∘ id = x :=
begin
  funext i,
  simp [function.comp,has_bind.bind,rand.bind],
  cases x i, refl
end

end rand

instance : monad rand :=
{ pure := @rand.pure
, bind := @rand.bind
, bind_assoc := @rand.bind_assoc
, pure_bind  := @rand.pure_bind
, id_map := @rand.id_map }

def range {α : Type u} [has_le α] (i j : α) :=
{ x : α // i ≤ x ∧ x ≤ j }

infix ` .. `:41 := range

class random (α : Type u) extends has_le α :=
(random : rand α)
(random_r : ∀ (x y : α),
              x ≤ y →
              rand (x .. y))
(random_series : generator → stream α)
(random_series_r : ∀ (x y : α),
                        x ≤ y →
                        generator →
                        stream (x .. y))

namespace tactic.interactive

meta def mk_generator : tactic generator := do
x ← time_in_nanos,
return $ generator.from_nat32 (bitvec.of_nat 32 x)

meta def tactic' (α : Type u) : Type (max u 1) := Π (β : Type), (α → tactic β) → tactic β

meta def run_rand' {α : Type u} (cmd : rand α) (β : Type) (tac : α → tactic β)
: tactic β := do
g ← mk_generator,
tac (cmd g).1

meta def run_rand {α : Type} (cmd : rand α) : tactic α := do
run_rand' cmd _ return

section random'

variables {α : Type u}
variable [random α]

meta def check_range : tactic unit :=
assumption <|> do
`[apply of_as_true, trivial]

meta def random' : tactic' α :=
run_rand' (random.random α)

meta def random_r' (x y : α) (p : x ≤ y . check_range) : tactic' (x .. y) :=
run_rand' (random.random_r x y p)

meta def random_series' : tactic' (stream α)
 | β cmd := do
g ← mk_generator,
cmd $ random.random_series α g

meta def random_series_r' (x y : α) (h : x ≤ y . check_range) : tactic' (stream $ x .. y)
 | β cmd := do
g ← mk_generator,
cmd $ random.random_series_r x y h g

end random'

section random

variable {α : Type}
variable [random α]

meta def random : tactic α :=
random' _ return

meta def random_r (x y : α) (p : x ≤ y . check_range) : tactic (x .. y) :=
random_r' _ _ p _ return

meta def random_series : tactic (stream α) :=
random_series' _ return

meta def random_series_r (x y : α) (h : x ≤ y . check_range) : tactic (stream $ x .. y) :=
random_series_r' _ _ h _ return

end random

end tactic.interactive

instance : preorder bool :=
{ le := λ p q, p → q
, le_refl := by { introv h, apply h }
, le_trans := by { introv ha hb h, apply hb, apply ha h } }

namespace bool

def coerce (x y : bool) (p : x ≤ y) (i : bool) : x .. y := do
  if hx : x ≤ i ∧ i ≤ y
  then ⟨ i, hx ⟩
  else ⟨ x , le_refl x , p ⟩

protected def get_random : rand bool :=
prod.map (λ v : bitvec 31, v.nth 14) id ∘ generator.next

structure bool_generator :=
  (next : bool)
  (queue : list bool)
  (gen : generator)

protected def first (g : generator) : bool_generator  :=
let (r,g') := generator.next g in
{ next := r.head
, queue := r.tail.to_list
, gen := g' }

protected def next : bool_generator → bool_generator
 | ⟨_,[],g⟩ := bool.first g
 | ⟨_,x::xs,g⟩ := ⟨x,xs,g⟩

def random_series' (g : generator) : stream bool_generator :=
stream.iterate bool.next (bool.first g)

def random_series (g : generator) : stream bool :=
stream.map bool.bool_generator.next $ random_series' g

end bool

instance : random bool :=
{ to_has_le := by apply_instance
, random   := bool.get_random
, random_r := λ x y p, bool.coerce _ _ p <$> bool.get_random
, random_series   := bool.random_series
, random_series_r := λ x y p g, stream.map (bool.coerce _ _ p) $ bool.random_series g }

instance (n : ℕ) : preorder (bitvec n) :=
{ le := λ x y, x.to_nat ≤ y.to_nat
, le_refl := by { introv, apply nat.le_refl }
, le_trans := by { introv ha hb, apply nat.le_trans ha hb } }

lemma bitvec.le_def {n : ℕ} (x y : bitvec n)
: x ≤ y ↔ x.to_nat ≤ y.to_nat :=
by refl

open nat

namespace stream

variable {α : Type u}

open list (length) stream (approx)

lemma length_approx
: ∀ (s : stream α) (n : ℕ), length (approx n s) = n
 | s 0 := rfl
 | s (succ n) := by simp [approx,length,one_add,length_approx]

end stream

def bitvec.random (n : ℕ) : rand (bitvec n) :=
λ g,
let r := bool.random_series' g,
    v := map bool.bool_generator.next $ stream.approx n r in
have Hv : length v = n,
     by { simp [stream.length_approx _ _], },
⟨ ⟨ v, Hv ⟩ , (r.nth $ succ n).gen ⟩

section coerce

parameters {i' r n : ℕ}
parameters {x y : bitvec n}

def x' := x.to_nat
def y' := y.to_nat

parameters P' : x' ≤ y'
include P'

lemma interval_fits_in_word_size
: x' + i' % (1 + (y' - x')) < 2^n :=
begin
  apply @lt_of_lt_of_le _ _ _ (x' + (y' - x' + 1)),
  { apply add_lt_add_left, simp,
    apply nat.mod_lt,
    rw one_add, apply zero_lt_succ },
  { rw [← add_assoc,← nat.add_sub_assoc P',nat.add_sub_cancel_left,add_one],
    clear P' x i', dunfold y',
    cases y with y Hy,
    unfold bitvec.to_nat vector.to_list subtype.val bitvec.bits_to_nat,
    rw [foldl_eq_foldr',← Hy, ← length_reverse],
    generalize : reverse y = x,
    clear Hy n,
    induction x,
    case nil
    { unfold foldr, refl },
    case cons x xs
    { simp [foldr,length,one_add,pow_succ,flip,bitvec.add_lsb],
      transitivity succ (1 +
       (foldr (λ (b : bool) (a : ℕ), a + (a + cond b 1 0)) 0 xs +
          foldr (λ (b : bool) (a : ℕ), a + (a + cond b 1 0)) 0 xs)),
      { apply succ_le_succ, apply add_le_add_right,
        cases x, apply zero_le, refl, },
      { rw [← add_succ,← add_succ,one_add,← succ_add,← two_mul],
        apply mul_le_mul_left,
        simp [flip,bitvec.add_lsb] at ih_1,
        apply ih_1 } } }
end

end coerce

def bitvec.coerce {n : ℕ} (x y : bitvec n) (P : x ≤ y)
  (i : bitvec n)
: (x .. y) :=
let x' := x.to_nat,
    y' := y.to_nat,
    i' := i.to_nat,
    r := i' % (y' - x' + 1) + x' in
have Hx : x ≤ bitvec.of_nat n r,
  begin
    unfold_local r,
    simp [bitvec.le_def,bitvec.to_nat_of_nat],
    rw [mod_eq_of_lt],
    { apply nat.le_add_right },
    apply interval_fits_in_word_size,
    apply P
  end,
have Hy : bitvec.of_nat n r ≤ y,
  begin
    unfold_local r,
    rw [bitvec.le_def,bitvec.to_nat_of_nat,mod_eq_of_lt],
    transitivity (y' - x') + x',
    { apply add_le_add_right,
      apply le_of_lt_succ,
      rw ← add_one,
      apply mod_lt,
      rw add_one, apply zero_lt_succ },
    { transitivity x' + (y' - x'),
      apply le_of_eq, ac_refl,
      rw [← nat.add_sub_assoc P,nat.add_sub_cancel_left], },
    simp, apply interval_fits_in_word_size P,
  end,
⟨ bitvec.of_nat _ r , Hx , Hy ⟩

def bitvec.random_series (n : ℕ) (g : generator) : stream (bitvec n) :=
stream.corec
(λ s, ⟨ stream.approx n s, stream.length_approx _ _ ⟩)
(stream.drop n)
(@random.random_series bool _ g)

instance random_bitvec (n : ℕ) : random (bitvec n) :=
{ to_has_le := by apply_instance
, random := bitvec.random n
, random_r := λ x y p, bitvec.coerce _ _ p <$> bitvec.random n
, random_series := bitvec.random_series n
, random_series_r := λ x y p g, bitvec.coerce _ _ p ∘ bitvec.random_series n g }

example : true :=
begin
(do x ← (tactic.interactive.random : tactic (bitvec 16)),
    tactic.trace (x : bitvec 16).to_nat),
(do x ← (tactic.interactive.random_series),
    tactic.trace $ map bitvec.to_nat (stream.approx 10 x : list (bitvec 16))),
(do x ← (tactic.interactive.random_series_r (25 : bitvec 15) 100),
    tactic.trace $ map (bitvec.to_nat ∘ subtype.val) (stream.approx 10 x)),
admit
end
