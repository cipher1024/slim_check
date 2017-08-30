
import ...test.slim_check.gen

universes u

namespace slim_check

variables (α : Type u)

class arbitrary :=
  (arby : gen α)

export arbitrary (arby)

open nat

instance arbitrary_nat : arbitrary ℕ :=
⟨ sized $ λ sz, fin.val <$> choose_any (fin $ succ sz) ⟩

instance arbitrary_int : arbitrary ℤ :=
⟨ sized $ λ sz, (λ n : fin _, n.val - int.of_nat sz ) <$> choose_any (fin $ succ $ 2 * sz) ⟩

variables {α}
variable [arbitrary α]

instance arbitrary_list : arbitrary (list α) :=
⟨ list_of (arby α) ⟩

instance arbitrary_prop : arbitrary Prop :=
{ arby := do
  x ← choose_any bool,
  return $ ↑x }

end slim_check
