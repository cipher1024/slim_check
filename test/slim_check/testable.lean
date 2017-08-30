
import ...test.slim_check.arbitrary

universes u v

variable α : Type u
variable β : α → Sort v
variable f : Type → Sort v

namespace slim_check

inductive test_result
| success
| gave_up : ℕ → test_result
| failure : (list string) → test_result

class testable (α : Sort u) :=
  (run : gen test_result)

open list


open test_result

instance imp_dec_testable (p : Prop) [decidable p] (β : p → Sort u)
  [∀ h, testable (β h)]
: testable (Π h, β h) :=
⟨ _,
  do
    if h : p
    then testable.run (β h)
    else return $ gave_up 1 ⟩

def add_to_counter_example (x : string) : test_result → test_result
 | (failure xs) := failure $ x :: xs
 | x := x

instance all_types_testable [testable (f ℤ)]
: testable (Π x, f x) :=
⟨ (Π x, f x),
  do
    r ← testable.run (f ℤ),
    return $ add_to_counter_example "ℤ" r ⟩

instance pi_testable [has_to_string α] [arbitrary α] [∀ x, testable (β x)]
: testable (Π x : α, β x) :=
⟨ (Π x : α, β x),
  gen.down $ do
  x ← arby α,
  gen.up (do
    r ← testable.run (β x),
    return $ add_to_counter_example (to_string x) r) ⟩

instance de_testable {p : Prop} [decidable p] : testable p :=
⟨ p, return $ if p then success else failure [] ⟩

section io

variable (α' : Sort u)
variable [testable α']

variable [io.interface]

open nat

def retry (cmd : rand test_result) : ℕ → rand test_result
 | 0 := return $ gave_up 1
 | (succ n) := do
r ← cmd,
match r with
 | success := return success
 | (failure xs) := return (failure xs)
 | (gave_up _) := retry n
end

def give_up_once (x : ℕ) : test_result → test_result
 | success := gave_up x
 | (gave_up n) := gave_up (n+x)
 | (failure xs) := failure xs

def testable.run_suite_aux : test_result → ℕ → rand test_result
 | r 0 := return r
 | r (succ n) := do
x ← retry (testable.run α' (99 - n)) 10,
match x with
 | success := testable.run_suite_aux r n
 | (failure xs) := return (failure xs)
 | (gave_up g) := testable.run_suite_aux (give_up_once g r) n
end

def testable.run_suite :=
testable.run_suite_aux α' success 100

def testable.check : io bool := do
x ← io.run_rand (testable.run_suite α'),
match x with
 | success := io.put_str_ln "Success!" >> return tt
 | (gave_up n) := io.put_str_ln ("Gave up " ++ repr n ++ " times") >> return tt
 | (failure xs) := do
   io.put_str_ln "\n===================",
   io.put_str_ln "Found problems!",
   io.put_str_ln "",
   list.mmap' io.put_str_ln xs,
   io.put_str_ln "-------------------",
   return ff
end

end io

end slim_check
