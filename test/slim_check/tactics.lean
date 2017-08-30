
import ...test.slim_check.testable

namespace tactic.interactive
open tactic slim_check

meta def expect_failure (cmd : itactic) : tactic unit :=
λ s, match cmd s with
| (interaction_monad.result.exception _ _ s') := (trace s' >> admit) s
| (interaction_monad.result.success a s) :=
   mk_exception "success_if_fail combinator failed, given tactic succeeded" none s
end


meta def trace_error (cmd : itactic) : tactic unit :=
λ s,
let r := cmd s in
match r with
| (interaction_monad.result.exception a b s') :=
(trace "\nBEGIN error" >> trace s' >> trace "END error"
  >> interaction_monad.result.exception a b) s'
| (interaction_monad.result.success a s) := r
end

meta def revert_all : tactic unit := do
xs ← local_context,
match xs with
 | (x :: xs) := tactic.revert x >> revert_all
 | [] := return ()
end


/-- build an instance of testable for the given proposition
  -/
meta def is_testable : tactic unit := do
(do
`(testable %%e) ← target,
match e with
 | (expr.pi n bi d t) := do
    p ← is_prop d,
    h ← to_expr ``(testable %%t) >>= λ e, tactic.assert `h (expr.pi n bi d e),
    solve1 (tactic.intro1 >> is_testable),
    if p
    then tactic.applyc `slim_check.imp_dec_testable
    else ((to_expr ``(slim_check.var_testable _ _ (some %%(reflect $ to_string n)))
           >>= tactic.apply) ; apply_instance)
 | _ := tactic.applyc `slim_check.de_testable
end)
<|> tactic.applyc `slim_check.de_testable

meta def slim_check : tactic unit := do
gs ← get_goals,
(do
revert_all,
t ← target,
p ← is_prop t,
when (¬ p) (fail "expecting a proposition"),
cl ←  to_expr ``(testable %%t),
hinst ← prod.snd <$> tactic.solve_aux cl is_testable,
 e ← to_expr ``(psigma.mk %%t %%hinst : Σ' t', testable t'),
 ⟨t',hinst⟩ ← eval_expr (psigma testable) e,
 r ← run_io (@testable.check t' hinst),
 if r then admit else fail "found counter examples")
 <|> (set_goals gs >> fail "found counter examples")

open interaction_monad.result.

end tactic.interactive
