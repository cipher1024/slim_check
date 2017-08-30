
import ...test.slim_check.testable

namespace tactic.interactive
open tactic slim_check

meta def revert_all : tactic unit := do
xs ← local_context,
match xs with
 | (x :: xs) := tactic.revert x >> revert_all
 | [] := return ()
end

meta def slim_check : tactic unit := do
revert_all,
t ← target,
p ← is_prop t,
when (¬ p) (fail "expecting a proposition"),
t' ← eval_expr Prop t,
e ← to_expr ``(testable.run %%t),
run ← eval_expr (gen test_result) e,
let hinst : testable t' := ⟨ _, run ⟩,
r ← run_io (@testable.check t' hinst),
if r then admit else fail "found counter examples"

open interaction_monad.result.

meta def expect_failure (cmd : itactic) : tactic unit :=
λ s, match cmd s with
| (interaction_monad.result.exception _ _ s') := (trace s' >> admit) s
| (interaction_monad.result.success a s) :=
   mk_exception "success_if_fail combinator failed, given tactic succeeded" none s
end

end tactic.interactive
