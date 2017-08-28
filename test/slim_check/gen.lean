import ...test.random

universes u

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
