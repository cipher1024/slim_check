
import system.io
import data.bitvec
import data.stream
import util.data.list
import util.data.fin
import system.io

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

meta def time_in_nanos : tactic ℕ :=
do time ← tactic.run_io (λ [ioi : io.interface],
          @io.cmd ioi { cmd := "gdate", args := [ "+%s%N" ] } ),
   pure time.to_nat

meta def check_range : tactic unit :=
assumption <|> do
`[apply of_as_true, trivial]

end tactic.interactive

export tactic.interactive (check_range)

namespace io

variable [io.interface]

def read_dev_random (n : ℕ) : io (array char n) := do
fh ← mk_file_handle "/dev/random" mode.read tt,
buf ← fs.read fh n,
fs.close fh,
if h : buf.size = n
then return (cast (by rw h) buf.to_array)
else io.fail "wrong number of bytes read from /dev/random"

def accum_char (w : bitvec 32) (c : char) : bitvec 32 :=
bitvec.of_nat _ c.to_nat + w.shl 8

def mk_generator : io generator := do
x ← io.read_dev_random 4,
return $ generator.from_nat32 (foldl accum_char 0 $ x.to_list)

variables {α : Type}

def run_rand (cmd : rand α) : io α := do
g ← io.mk_generator,
return (cmd g).1

variable [random α]

def random : io α :=
io.run_rand (random.random α)

def random_r (x y : α) (p : x ≤ y . check_range) : io (x .. y) :=
io.run_rand (random.random_r x y p)

def random_series : io (stream α) := do
g ← io.mk_generator,
return $ random.random_series α g

def random_series_r (x y : α) (h : x ≤ y . check_range) : io (stream $ x .. y) := do
g ← io.mk_generator,
return $ random.random_series_r x y h g

end io

namespace tactic.interactive

meta def mk_generator : tactic generator := do
tactic.run_io @io.mk_generator

meta def tactic' (α : Type u) : Type (max u 1) :=
Π (β : Type), (α → tactic β) → tactic β

meta def run_rand' {α : Type u} (cmd : rand α) (β : Type) (tac : α → tactic β)
: tactic β := do
g ← mk_generator,
tac (cmd g).1

section random'

variables {α : Type u}
variable [random α]

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
tactic.trace "\n\n",
(do x ← (tactic.interactive.random : tactic (bitvec 16)),
    tactic.trace (x : bitvec 16).to_nat),
(do x ← (tactic.interactive.random_series),
    tactic.trace $ map bitvec.to_nat (stream.approx 10 x : list (bitvec 16))),
(do x ← (tactic.interactive.random_series_r (25 : bitvec 15) 100),
    tactic.trace $ map (bitvec.to_nat ∘ subtype.val) (stream.approx 10 x)),
admit
end

meta def main [io.interface] : io unit := do
print_ln "\n\n",
x ← (io.random : io (bitvec 16)),
print_ln (x : bitvec 16).to_nat,
x ← io.random_series,
print_ln $ map bitvec.to_nat (stream.approx 10 x : list (bitvec 16)),
x ← (io.random_series_r (25 : bitvec 15) 100),
print_ln $ map (bitvec.to_nat ∘ subtype.val) (stream.approx 10 x)

run_cmd tactic.run_io @main

lemma div_two_round_up
  (x : ℕ)
  (h₀ : 1 < x)
: (x + 1) / 2 < x :=
begin
  rw [div_lt_iff_lt_mul,norm_num.mul_bit0,mul_one,bit0],
  apply add_lt_add_left, apply h₀,
  apply of_as_true, trivial
end

def word_size : ℕ → ℕ
 | x :=
if h : 1 < x then
  have (x + 1) / 2 < x,
    from div_two_round_up _ h,
  succ $ word_size ((x + 1) / 2)
else 0

#eval word_size 15
#eval 2 ^ word_size 8

lemma word_size_le_two_pow (n : ℕ)
: n ≤ 2^word_size n :=
begin
  apply nat.strong_induction_on n,
  clear n, intros n IH,
  by_cases 1 < n with h,
  { rw [word_size,if_pos h,pow],
    cases n with n, { cases not_lt_zero _ h },
    change n < _,
    rw ← @div_lt_iff_lt_mul _ _ 2 dec_trivial,
    have h' := div_two_round_up (succ n) h,
    specialize IH ((succ n + 1) / 2) h', clear h h',
    rw [succ_add,← add_succ] at *,
    simp at *,
    have h : (n + 2 * 1) / 2 = n / 2 + 1 :=
       add_mul_div_left _ _ dec_trivial,
    rw [mul_one] at h,
    rw h at IH ⊢,
    apply IH },
  { rw [word_size,if_neg h,pow],
    apply le_of_not_gt h }
end

namespace fin
section fin
parameter {n : ℕ}
def w := word_size (succ n)

def bitvec.to_fin (v : bitvec w) : fin (succ n) :=
fin.of_nat v.to_nat

protected def to_bitvec (v : fin (succ n)) : bitvec w :=
bitvec.of_nat _ v.val

protected def random : rand (fin (succ n)) :=
bitvec.to_fin <$> random.random (bitvec w)

protected def random_series (g : generator) : stream (fin (succ n)) :=
stream.map bitvec.to_fin $ @random.random_series (bitvec w) _ g

lemma val_lt_word_size (z : fin (succ n))
: z.val < (2 : ℕ) ^ w :=
lt_of_lt_of_le z.is_lt (word_size_le_two_pow _)

lemma bitvec_to_nat_to_bitvec (x : fin (succ n))
: bitvec.to_nat (fin.to_bitvec x) = x.val :=
begin
  rw [fin.to_bitvec,bitvec.to_nat_of_nat,mod_eq_of_lt],
  apply val_lt_word_size
end

lemma fin_val_bitvec_to_fin
  {x : bitvec w} (hn : x.to_nat < succ n)
: (bitvec.to_fin x).val = x.to_nat :=
by simp [bitvec.to_fin,fin.val_of_nat hn]

protected def of_bitvec_range (x y : fin (succ n))
: range x.to_bitvec y.to_bitvec → range x y
 | ⟨i,hx,hy⟩ :=
have hn : bitvec.to_nat i < nat.succ n,
  by { rw [bitvec.le_def,bitvec_to_nat_to_bitvec] at hy,
       apply lt_of_le_of_lt hy y.is_lt },
have hx' : x ≤ bitvec.to_fin i,
  by { simp [bitvec.le_def,bitvec_to_nat_to_bitvec] at hx,
       simp [fin.le_def,fin_val_bitvec_to_fin hn,hx], },
have hy' : bitvec.to_fin i ≤ y,
  by { simp [bitvec.le_def,bitvec_to_nat_to_bitvec] at hy,
       simp [fin.le_def,fin_val_bitvec_to_fin hn,hy], },
⟨bitvec.to_fin i,hx',hy'⟩

protected def random_r (x y : fin (succ n)) (p : x ≤ y) : rand (x .. y) :=
have x.to_bitvec ≤ y.to_bitvec,
  by { simp [bitvec.le_def,bitvec_to_nat_to_bitvec],
       rw ← fin.le_def, apply p },
of_bitvec_range _ _ <$> @random.random_r (bitvec w) _ _ _ this

protected def random_series_r (x y : fin (succ n)) (p : x ≤ y)
  (g : generator)
: stream (x .. y) :=
have x.to_bitvec ≤ y.to_bitvec,
  by { simp [bitvec.le_def,bitvec_to_nat_to_bitvec],
       rw ← fin.le_def, apply p },
stream.map (of_bitvec_range _ _) $ @random.random_series_r (bitvec w) _ _ _ this g

end fin
end fin

instance fin_random (n : ℕ) : random (fin (succ n)) :=
{ to_has_le := by apply_instance
, random := fin.random
, random_r := λ x y p, @fin.random_r n x y p
, random_series := fin.random_series
, random_series_r := λ x y p, @fin.random_series_r n x y p }

section
open stream
variable [io.interface]
def try_fin_random : io unit := do
put_str_ln "",
x ← (io.random : io (fin 10)), print_ln x,
x ← (io.random_r (2 : fin 10) 7 : io _), print_ln (x.val),
x ← (io.random_series : io (stream (fin 10))), print_ln $ approx 10 x

end

run_cmd tactic.run_io @try_fin_random
