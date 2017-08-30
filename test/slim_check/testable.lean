
import ...test.slim_check.arbitrary

universes u v

variable α : Type u
variable β : α → Sort v
variable f : Type → Sort v

namespace slim_check

class testable (α : Sort u) :=
  (run : gen (option (list string)))

open list

instance all_types_testable [testable (f ℤ)]
: testable (Π x, f x) :=
⟨ (Π x, f x),
  do
    r ← testable.run (f ℤ),
    return $ (cons $ "ℤ") <$> r ⟩

instance pi_testable [has_to_string α] [arbitrary α] [∀ x, testable (β x)]
: testable (Π x : α, β x) :=
⟨ (Π x : α, β x),
  gen.down $ do
  x ← arby α,
  gen.up (do
    r ← testable.run (β x),
    return $ (cons $ to_string x) <$> r) ⟩

instance de_testable {p : Prop} [decidable p] : testable p :=
⟨ p, return $ if p then none else some [] ⟩

section io

variable (α' : Sort u)
variable [testable α']

variable [io.interface]

open nat

def testable.run_suite_aux : ℕ → rand (option (list string))
 | 0 := return none
 | (succ n) := do
x ← testable.run α' (99 - n),
option.rec_on x (testable.run_suite_aux n) (return ∘ some)

def testable.run_suite :=
testable.run_suite_aux α' 100

def testable.check : io unit := do
x ← io.run_rand (testable.run_suite α'),
match x with
 | none := io.put_str_ln "Success!"
 | (some xs) := do
   io.put_str_ln "\n===================",
   io.put_str_ln "Found problems!",
   io.put_str_ln "",
   list.mmap' io.put_str_ln xs,
   io.put_str_ln "-------------------"
end

end io

end slim_check
