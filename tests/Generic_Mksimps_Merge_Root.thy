(* Merging, the common ancestor: merge.foo on P x and merge.bar on R x. *)

theory Generic_Mksimps_Merge_Root
  imports Generic_Mksimps_Test_Base
begin

setup \<open>
  Simplifier.map_theory_simpset
   (add_handler "merge.foo" {patterns = [\<^prop>\<open>P x\<close>], priority = 0, kept = true} pass #>
    add_handler "merge.bar" {patterns = [\<^prop>\<open>R x\<close>], priority = 0, kept = true} pass)
\<close>

ML \<open>
val right_mksimps = "right mksimps function";

(*the handlers called on s assumed, and whether the right parent's mksimps function was called*)
fun merge_calls ctxt s =
  let val names = call_names (dispatch_calls ctxt (assume_prop ctxt s))
  in (filter_out (equal right_mksimps) names, member (op =) names right_mksimps) end;

fun foo_patterns ctxt =
  AList.lookup (op =) (#mksimps_handlers (Simplifier.dest_ss (Simplifier.simpset_of ctxt)))
    "merge.foo"
  |> Option.map #patterns;
\<close>

end
