
import ...test.slim_check.arbitrary

universes u v

variable α : Type u
variable β : α → Prop
variable f : Type → Prop

namespace slim_check

inductive test_result (p : Prop)
| success {} : test_result
| gave_up {} : ℕ → test_result
| failure : ¬ p → (list string) → test_result

class testable (p : Prop) :=
  (run : gen (test_result p))

open list


open test_result

def add_to_counter_example (x : string) {p q : Prop}
  (h : q → p)
: test_result p → test_result q
 | (failure Hce xs) := failure (mt h Hce) $ x :: xs
 | success := success
 | (gave_up n) := gave_up n

def convert_counter_example {p q : Prop}
  (h : q → p)
: test_result p → test_result q
 | (failure Hce xs) := failure (mt h Hce) xs
 | success := success
 | (gave_up n) := gave_up n

instance imp_dec_testable (p : Prop) [decidable p] (β : p → Prop)
  [∀ h, testable (β h)]
: testable (Π h, β h) :=
⟨ do
    if h : p
    then convert_counter_example ($ h) <$> testable.run (β h)
    else return $ gave_up 1 ⟩

instance all_types_testable [testable (f ℤ)]
: testable (Π x, f x) :=
⟨ do
    r ← testable.run (f ℤ),
    return $ add_to_counter_example "ℤ" ($ ℤ) r ⟩

def var_testable [has_to_string α] [arbitrary α] [∀ x, testable (β x)]
  (var : option string := none)
: testable (Π x : α, β x) :=
⟨ gen.down $ do
  x ← arby α,
  gen.up (do
    r ← testable.run (β x),
    return $ match var with
     | none := add_to_counter_example (to_string x) ($ x) r
     | (some v) := add_to_counter_example (v ++ " := " ++ to_string x) ($ x) r
    end) ⟩

instance pi_testable [has_to_string α] [arbitrary α] [∀ x, testable (β x)]
: testable (Π x : α, β x) :=
var_testable α β

instance de_testable {p : Prop} [decidable p] : testable p :=
⟨ return $ if h : p then success else failure h [] ⟩

section io

variable (α' : Prop)
variable [testable α']

variable [io.interface]

open nat

variable {α'}

def retry (cmd : rand (test_result α')) : ℕ → rand (test_result α')
 | 0 := return $ gave_up 1
 | (succ n) := do
r ← cmd,
match r with
 | success := return success
 | (failure Hce xs) := return (failure Hce xs)
 | (gave_up _) := retry n
end

def give_up_once (x : ℕ) : test_result α' → test_result α'
 | success := gave_up x
 | (gave_up n) := gave_up (n+x)
 | (failure Hce xs) := failure Hce xs

variable (α')

def testable.run_suite_aux : test_result α' → ℕ → rand (test_result α')
 | r 0 := return r
 | r (succ n) := do
x ← retry (testable.run α' (99 - n)) 10,
match x with
 | success := testable.run_suite_aux r n
 | (failure Hce xs) := return (failure Hce xs)
 | (gave_up g) := testable.run_suite_aux (give_up_once g r) n
end

def testable.run_suite :=
testable.run_suite_aux α' success 100

def testable.check : io bool := do
x ← io.run_rand (testable.run_suite α'),
match x with
 | success := return tt
 | (gave_up n) := io.put_str_ln ("Gave up " ++ repr n ++ " times") >> return tt
 | (failure _ xs) := do
   io.put_str_ln "\n===================",
   io.put_str_ln "Found problems!",
   io.put_str_ln "",
   list.mmap' io.put_str_ln xs,
   io.put_str_ln "-------------------",
   return ff
end

end io

end slim_check
