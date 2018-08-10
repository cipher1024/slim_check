
import test.slim_check.testable

namespace tactic.interactive
open tactic slim_check

meta def expect_failure (cmd : itactic) : tactic unit :=
λ s, match cmd s with
| (interaction_monad.result.exception msg _ s') :=
  match msg with
   | (some msg') := (trace (msg' ()) >> admit) s'
   | none := admit s'
  end
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

meta def applye (e : pexpr) : tactic unit := do
() <$ (to_expr e >>= tactic.apply)

/-- build an instance of testable for the given proposition
  -/
meta def is_testable : tactic unit := do
(do
tactic.target >>= instantiate_mvars >>= tactic.change,
`(testable %%e) ← target,
match e with
 | (expr.pi n bi d t) :=
   if bi = binder_info.inst_implicit then do
      h ← tactic.assert `h d,
      solve1 apply_instance,
      applye ``(@slim_check.test_one _ _ %%h _),
      is_testable
   else do
    trace "there",
    p ← is_prop d,
    let var := reflect $ to_string n,
    let mk_testable_inst := (do
          h ← to_expr ``(testable %%t) >>= λ e, tactic.assert `h (expr.pi n bi d e),
          solve1 (tactic.intro1 >> target >>= trace >> is_testable)),
    if p then do
       trace "A",
       mk_testable_inst,
       trace "mid A",
       tactic.applyc `slim_check.imp_dec_testable,
       trace "end A"
    else if d = `(Type) then do
      trace "B",
      let t' := expr.instantiate_local n `(ℤ) t,
      h ← to_expr ``(testable %%t') >>= tactic.assert `h,
      solve1 is_testable,
      applye ``(slim_check.test_one _ _ ℤ (some (%%var,"ℤ"))) ; apply_instance
      -- let specialize := (λ (sp : expr) (nm : string), do
      --     let t' := expr.instantiate_local n sp t,
      --     h ← to_expr ``(testable %%t') >>= tactic.assert `h,
      --     solve1 is_testable,
      --     let type := reflect nm,
      --     applye ``(slim_check.test_one _ _ %%sp (some (%%var,%%type)))
      --       ; apply_instance),
      -- apply ``(slim_check.combine_testable _ [_,_] _),
      -- specialize `(ℤ) "ℤ",
      -- specialize `(list ℤ) "list ℤ",
      -- apply ``(nat.zero_lt_succ)
    else do
       mk_testable_inst,
       (  (applye ``(slim_check.test_forall_in_list _ _ %%var)  ; apply_instance)
         <|>
          (applye ``(slim_check.var_testable _ _ (some %%var)) ; apply_instance))
 | _ := trace_error $ tactic.applyc `slim_check.de_testable
end)
<|> trace_error (tactic.applyc `slim_check.de_testable)

open slim_check.test_result nat

meta def slim_check : tactic unit :=
do n ← revert_all,
   t ← target,
   p ← is_prop t,
   when (¬ p) (fail "expecting a proposition"),
   trace "so far",
   cl ←  to_expr ``(testable %%t),
   hinst ← prod.snd <$> tactic.solve_aux cl is_testable,
   trace "so far",
   expr.has_meta_var <$> (tactic.result >>= instantiate_mvars) >>= trace,
   e ← to_expr ``(psigma.mk %%t %%hinst : Σ' t', testable t'),
   expr.has_meta_var <$> (tactic.result >>= instantiate_mvars) >>= trace,
   ⟨t',hinst⟩ ← eval_expr (psigma testable) e,
   expr.has_meta_var <$> (tactic.result >>= instantiate_mvars) >>= trace,
   r ← unsafe_run_io (@testable.check t' hinst),
   expr.has_meta_var <$> (tactic.result >>= instantiate_mvars) >>= trace,
   trace t,
   match r with
    | (success (psum.inl ())) := admit
    | (success (psum.inr p)) := do `[apply @of_as_true %%t, exact trivial]
                                -- if some testable instances are not based on decidable
                                -- the above might fail. The best would be to run
                                -- the gen
    | (failure _ xs) := do
      intron n,
      fail $ string.intercalate "\n" $
        [ "\n==================="
        , "Found problems!"
        , "" ] ++
        xs ++
        [ "-------------------" ]
    | (gave_up n) := trace ("Gave up " ++ repr n ++ " time(s)") >> admit
   end,
   expr.has_meta_var <$> (tactic.result >>= instantiate_mvars) >>= trace

open interaction_monad.result.

end tactic.interactive
