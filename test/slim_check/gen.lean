import ...test.random

universes u v

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

variable (α : Type u)

section random

variable [random α]

def choose_any : gen α :=
λ _, random.random α

variables {α}

def choose (x y : α) (p : x ≤ y . check_range) : gen (x .. y) :=
λ _, random.random_r x y p

end random

open nat

def choose_nat (x y : ℕ) (p : x ≤ y . check_range) : gen (x .. y) := do
⟨z,h⟩ ← @choose (fin $ succ y) _ ⟨x,succ_le_succ p⟩ ⟨y,lt_succ_self _⟩ p,
have h' : x ≤ z.val ∧ z.val ≤ y,
  by { simp [fin.le_def] at h, apply h },
return ⟨z.val,h'⟩


open nat

namespace gen

variable {α}
def up (x : gen α) : gen (ulift.{v} α) :=
λ sz g, prod.rec_on (x sz g) (prod.mk ∘ ulift.up)

def down (x : gen (ulift.{v} α)) : gen α :=
λ sz g, prod.rec_on (x sz g) (prod.mk ∘ ulift.down)

lemma up_down {α : Type u} (b : gen $ ulift.{v} α)
: up (down b) = b :=
begin
  funext x y, simp [up,down],
  destruct (b x y),
  intros z g h, rw h,
  change (_,_) = _,
  rw ulift.up_down
end

lemma down_up {α : Type u} (a : gen α)
: down (up a) = a :=
begin
  funext i j, simp [up,down],
  destruct (a i j),
  intros z g h, rw h,
end

end gen

variable {α}

def sized (cmd : ℕ → gen α) : gen α :=
λ sz, cmd sz sz

def vector_of : ∀ (n : ℕ) (cmd : gen α), gen (vector α n)
 | 0 _ := return vector.nil
 | (succ n) cmd := vector.cons <$> cmd <*> vector_of n cmd

def list_of (cmd : gen α) : gen (list α) :=
sized $ λ sz, do
⟨ n ⟩ ← gen.up $ choose_nat 0 sz,
v ← vector_of n.val cmd,
return v.to_list
