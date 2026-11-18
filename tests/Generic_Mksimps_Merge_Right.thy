(* Merging, the right parent: merge.foo untouched; merge.right on P2 x, not kept by clear_simpset;
   a mksimps function that logs its calls. *)

theory Generic_Mksimps_Merge_Right
  imports Generic_Mksimps_Merge_Root
begin

setup \<open>
  Simplifier.map_theory_simpset
   (add_handler "merge.right" {patterns = [\<^prop>\<open>P2 x\<close>], priority = 0, kept = false} pass #>
    (fn ctxt =>
      let val mk = Simplifier.get_mksimps_context ctxt in
        Simplifier.set_mksimps_context (fn th => fn ctxt' =>
          (log_call ctxt' (right_mksimps, th); mk th ctxt')) ctxt
      end))
\<close>

end
