(* Checks of merging (section 6 of ai-artifacts/GENERIC_MKSIMPS_PLAN.md, items 11, 12 and 14):
   the right parent comes first.  Any failing check fails the build. *)

theory Generic_Mksimps_Merge_Swapped
  imports Generic_Mksimps_Merge_Right Generic_Mksimps_Merge_Left
begin

ML \<open>
local
  val ctxt = \<^context>;
in
  val _ = check "11: same name, the first parent's version"
    (foo_patterns ctxt = SOME [read_prop ctxt "P ?x"]);
  val _ = check "11: same name, its pattern" (merge_calls ctxt "P a" = (["merge.foo"], true));
  val _ = check "11: same name, the other pattern" (merge_calls ctxt "Q a" = ([], true));
  val _ = check "11: one handler through two import paths"
    (merge_calls ctxt "R a" = (["merge.bar"], true));
  val _ = check "12: the calling order does not depend on the import order"
    (merge_calls ctxt "P2 a" = (["merge.left", "merge.right"], true));
  val _ = check "11: the first parent's mksimps function" (merge_calls ctxt "C" = ([], true));
  val _ = check "14: flags after merging"
    (merge_calls (Simplifier.clear_simpset ctxt) "P2 a" = (["merge.left"], true));
end
\<close>

end
