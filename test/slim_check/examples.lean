
import ...test.slim_check.tactics

namespace slim_check.examples

example : ∀ n : ℕ, n > n+1 :=
by expect_failure { slim_check }

example : ∀ n : ℕ, n < n+1 :=
by expect_failure { slim_check }

example : 1 < (2 : ℕ) :=
by slim_check

end slim_check.examples
