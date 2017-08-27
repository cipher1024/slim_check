
import system.io
import data.bitvec

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

def next : generator → bitvec 32 × generator
  | ⟨ s1, s2 ⟩ :=
	let	k    := s1.to_int / 53668,
		s1'  := 40014 * (s1.to_int - k * 53668) - k * 12211,
		s1'' := if s1' < 0 then s1' + 2147483563 else s1',

		k'   := s2.to_int / 52774,
		s2'  := 40692 * (s2.to_int - k' * 52774) - k' * 3791,
		s2'' := if s2' < 0 then s2' + 2147483399 else s2',
                z    := s1'' - s2'',
                z'   := if z < 1 then z + 2147483562 else z
in ⟨ bitvec.of_int _ z', bitvec.of_int _ s1'', bitvec.of_int _ s2'' ⟩

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

open lean.parser
open interactive
open interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def funext1 (x : parse ident_ ?) : tactic unit := do
`[apply funext],
intro x

meta def funext : parse ident_ * → tactic unit
 | [] := return ()
 | (x :: xs) := funext1 x >> funext xs

end tactic.interactive

def rand (α : Type u) := generator → generator × α

namespace rand

variables {α β γ : Type u}

protected def pure (x : α) : rand α :=
λ g, (g,x)

protected def bind (x : rand α) (f : α → rand β) : rand β :=
λ g,
let r := x g in
f r.2 r.1

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

def gen (α : Type u) := ℕ → rand α

namespace gen

variables {α β γ : Type u}

protected def pure (x : α) : gen α :=
λ _, pure x

protected def bind (x : gen α) (f : α → gen β) : gen β
 | sz := do
i ← x sz,
f i sz

instance : has_bind gen :=
⟨ @gen.bind ⟩

instance : has_pure gen :=
⟨ @gen.pure ⟩

lemma bind_assoc (x : gen α) (f : α → gen β) (g : β → gen γ)
: x >>= f >>= g = x >>= (λ i, f i >>= g) :=
begin
  funext sz,
  simp [has_bind.bind],
  simp [gen.bind,monad.bind_assoc],
end

lemma pure_bind (x : α) (f : α → gen β)
: pure x >>= f = f x :=
begin
  funext i,
  simp [has_bind.bind],
  simp [gen.bind,monad.pure_bind],
  refl
end

lemma id_map (x : gen α)
: x >>= pure ∘ id = x :=
begin
  funext i,
  simp [has_bind.bind,function.comp,pure,has_pure.pure],
  simp [gen.bind,gen.pure],
  rw monad.bind_pure,
  exact α,
end

end gen

instance : monad gen :=
{ pure := @gen.pure
, bind := @gen.bind
, bind_assoc := @gen.bind_assoc
, pure_bind  := @gen.pure_bind
, id_map := @gen.id_map }

namespace tactic.interactive
open tactic

meta def slim_check : tactic unit := do
t ← target,
p ← is_prop t,
when (¬ p) (fail "expecting a proposition"),
`[apply of_as_true, trivial]

meta def expect_failure (cmd : itactic) : tactic unit := do
x ← try_core cmd,
match x with
 | (some x) := fail "tactic is expected to fail"
 | none := admit
end

end tactic.interactive

example : ∀ n : ℕ, n > n+1 :=
by expect_failure { slim_check }

example : ∀ n : ℕ, n < n+1 :=
by expect_failure { slim_check }

example : 1 < (2 : ℕ) :=
by slim_check
