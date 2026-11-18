(* Checks of merging (section 6 of ai-artifacts/GENERIC_MKSIMPS_PLAN.md, items 11, 12 and 14):
   the left parent comes first.  Any failing check fails the build. *)

theory Generic_Mksimps_Merge
  imports Generic_Mksimps_Merge_Left Generic_Mksimps_Merge_Right
begin

ML \<open>
local
  val ctxt = \<^context>;
in
  val _ = check "11: same name, the first parent's version"
    (foo_patterns ctxt = SOME [read_prop ctxt "Q ?x"]);
  val _ = check "11: same name, old pattern" (merge_calls ctxt "P a" = ([], false));
  val _ = check "11: same name, new pattern" (merge_calls ctxt "Q a" = (["merge.foo"], false));
  val _ = check "11: one handler through two import paths"
    (merge_calls ctxt "R a" = (["merge.bar"], false));
  val _ = check "11: different names from both parents"
    (merge_calls ctxt "P2 a" = (["merge.left", "merge.right"], false));
  val _ = check "11: the first parent's mksimps function" (merge_calls ctxt "C" = ([], false));
  val _ = check "14: flags after merging"
    (merge_calls (Simplifier.clear_simpset ctxt) "P2 a" = (["merge.left"], false));
end
\<close>

end
