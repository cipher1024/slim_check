
import ...test.slim_check.tactics

namespace slim_check.examples

example : ∀ n : ℕ, n > n+1 :=
by expect_failure { slim_check }

open slim_check

run_cmd tactic.run_io $ @testable.check (∀ n : ℕ, n > n+1)  _
run_cmd tactic.run_io $ @testable.check (∀ n m : ℕ, n ≤ m)  _
run_cmd tactic.run_io $ @testable.check (∀ n m : ℕ, 2*m + n < 100)  _
run_cmd tactic.run_io $ @testable.check (∀ n m : ℕ, 0 ≤ m + n)  _
run_cmd tactic.run_io $ @testable.check
                     (∀ (n : ℤ) (xs : list ℤ) x,
                                 x ∈ xs → x < n)  _

example : ∀ n : ℕ, n < n+1 :=
by slim_check

example : 1 < (2 : ℕ) :=
by slim_check

def even (n : ℕ) : bool :=
n % 2 = 0

example : (∀ (α : Type) (xs : list α), xs.length < 10) :=
by expect_failure { slim_check }

example : (∀ (α : Type) (xs : list α), xs.length < 10) :=
by expect_failure { slim_check }

example : (∀ n m : ℕ, 2*m + n < 100) :=
by expect_failure { slim_check }

example : (∀ (n : ℤ) (xs : list ℤ) x, x ∈ xs → x ≤ n) :=
by expect_failure { slim_check }

example : (∀ n m : ℕ, even m → ¬ even n → ¬ even (m+n)) :=
by slim_check

variables n m : ℕ

example : (even m → ¬ even n → ¬ even (m+n)) :=
by slim_check

end slim_check.examples
