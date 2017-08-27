
import system.io
import data.bitvec
-- import control.applicative.

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

def random (α : Type u) := generator → generator × α

def gen (α : Type u) := ℕ → random α
