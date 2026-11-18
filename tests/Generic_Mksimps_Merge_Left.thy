(* Merging, the left parent: merge.foo registered again, now on Q x; merge.left on P2 x, kept by
   clear_simpset. *)

theory Generic_Mksimps_Merge_Left
  imports Generic_Mksimps_Merge_Root
begin

setup \<open>
  Simplifier.map_theory_simpset
   (add_handler "merge.foo" {patterns = [\<^prop>\<open>Q x\<close>], priority = 0, kept = true} pass #>
    add_handler "merge.left" {patterns = [\<^prop>\<open>P2 x\<close>], priority = 0, kept = true} pass)
\<close>

end
