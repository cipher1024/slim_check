
namespace tactic.interactive
open tactic

meta def slim_check : tactic unit := do
t ← target,
p ← is_prop t,
when (¬ p) (fail "expecting a proposition"),
`[apply of_as_true, trivial]

meta def expect_failure (cmd : itactic) : tactic unit := do
x ← try_core cmd,
match x with
 | (some x) := fail "tactic is expected to fail"
 | none := admit
end

end tactic.interactive
