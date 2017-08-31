
import ...test.slim_check.arbitrary

universes u v

variable α : Type u
variable β : α → Prop
variable f : Type → Prop

namespace slim_check

inductive test_result (p : Prop)
| success : (psum unit p) → test_result
| gave_up {} : ℕ → test_result
| failure : ¬ p → (list string) → test_result

class testable (p : Prop) :=
  (run : gen (test_result p))

open list

open test_result

def combine {p q : Prop} : psum unit (p → q) → psum unit p → psum unit q
 | (psum.inr f) (psum.inr x) := psum.inr (f x)
 | _ _ := psum.inl ()

def convert_counter_example {p q : Prop}
  (h : q → p)
: test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q
 | (failure Hce xs) _ := failure (mt h Hce) xs
 | (success Hp) Hpq := success (combine Hpq Hp)
 | (gave_up n) _ := gave_up n

def add_to_counter_example (x : string) {p q : Prop}
  (h : q → p)
: test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q
 | (failure Hce xs) _ := failure (mt h Hce) $ x :: xs
 | r hpq := convert_counter_example h r hpq

def add_var_to_counter_example {γ : Type v} [has_to_string γ]
  (var : string) (x : γ) {p q : Prop}
  (h : q → p)
: test_result p →
  opt_param (psum unit (p → q)) (psum.inl ()) →
  test_result q :=
@add_to_counter_example (var ++ " := " ++ to_string x) _ _ h

instance imp_dec_testable (p : Prop) [decidable p] (β : p → Prop)
  [∀ h, testable (β h)]
: testable (Π h, β h) :=
⟨ do
    if h : p
    then (λ r, convert_counter_example ($ h) r (psum.inr $ λ q _, q)) <$> testable.run (β h)
    else return $ gave_up 1 ⟩

instance all_types_testable [testable (f ℤ)]
: testable (Π x, f x) :=
⟨ do
    r ← testable.run (f ℤ),
    return $ add_to_counter_example "ℤ" ($ ℤ) r ⟩

def test_one (x : α) [testable (β x)] (var : option (string × string) := none)
: testable (Π x, β x) :=
⟨ do
    r ← testable.run (β x),
    return $ match var with
     | none := convert_counter_example ($ x) r
     | (some (v,x_str)) := add_var_to_counter_example v x_str ($ x) r
    end ⟩

def test_forall_in_list (var : string) [∀ x, testable (β x)] [has_to_string α]
: Π xs : list α, testable (∀ x, x ∈ xs → β x)
 | [] := ⟨ return $ success $ psum.inr (by { introv h, cases h} ) ⟩
 | (x :: xs) :=
⟨ do
    r ← testable.run (β x),
    match r with
     | failure _ _ := return $ add_var_to_counter_example var x
                               (by { intro h, apply h, left, refl }) r
     | success hp := do
       rs ← (test_forall_in_list xs).run,
       return $ convert_counter_example
                               (by { intros h i h',
                                     apply h,
                                     right, apply h' })
                               rs
                               (combine (psum.inr
                                $ by { intros j h, simp only [ball_cons],
                                       split ; assumption, } ) hp)
     | gave_up n := do
       rs ← (test_forall_in_list xs).run,
       match rs with
        | (success _) := return $ gave_up n
        | (failure Hce xs) := return $ failure
                    (by { simp only [ball_cons],
                          apply not_and_of_not_right _ Hce, }) xs
        | (gave_up n') := return $ gave_up (n + n')
       end
    end ⟩

def var_testable [has_to_string α] [arbitrary α] [∀ x, testable (β x)]
  (var : option string := none)
: testable (Π x : α, β x) :=
⟨ gen.down $ do
  x ← arby α,
  gen.up (do
    r ← testable.run (β x),
    return $ match var with
     | none := add_to_counter_example (to_string x) ($ x) r
     | (some v) := add_var_to_counter_example v x ($ x) r
    end) ⟩

instance pi_testable [has_to_string α] [arbitrary α] [∀ x, testable (β x)]
: testable (Π x : α, β x) :=
var_testable α β

instance de_testable {p : Prop} [decidable p] : testable p :=
⟨ return $ if h : p then success (psum.inr h) else failure h [] ⟩

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
 | success hp := return $ success hp
 | (failure Hce xs) := return (failure Hce xs)
 | (gave_up _) := retry n
end

def give_up_once (x : ℕ) : test_result α' → test_result α'
 | (success (psum.inl ())) := gave_up x
 | (success (psum.inr p))  := success (psum.inr p)
 | (gave_up n) := gave_up (n+x)
 | (failure Hce xs) := failure Hce xs

variable (α')

def testable.run_suite_aux : test_result α' → ℕ → rand (test_result α')
 | r 0 := return r
 | r (succ n) := do
x ← retry (testable.run α' (99 - n)) 10,
match x with
 | (success (psum.inl ())) := testable.run_suite_aux r n
 | (success (psum.inr Hp)) := return $ success (psum.inr Hp)
 | (failure Hce xs) := return (failure Hce xs)
 | (gave_up g) := testable.run_suite_aux (give_up_once g r) n
end

def testable.run_suite :=
testable.run_suite_aux α' (success $ psum.inl ()) 100

def testable.check : io (test_result α') :=
io.run_rand (testable.run_suite α')

def testable.check' : io bool := do
x ← io.run_rand (testable.run_suite α'),
match x with
 | (success _) := return tt
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
