(* Constants and ML helpers shared by the generic_mksimps tests. *)

theory Generic_Mksimps_Test_Base
  imports Main
begin

consts R :: "nat \<Rightarrow> bool"  f :: "nat \<Rightarrow> nat"  g :: "nat \<Rightarrow> bool"  h :: "nat \<Rightarrow> bool"
  C :: bool  S :: "nat set"

text \<open>\<open>P\<close>, \<open>Q\<close> and \<open>P2\<close> are definitions, so that \<open>P x \<Longrightarrow> Q x\<close> and \<open>P x = P2 x\<close> are lemmas, while
  the default simpset leaves \<open>P a\<close>, \<open>Q a\<close>, \<open>P2 a\<close> alone.\<close>

definition P :: "nat \<Rightarrow> bool" where "P x \<longleftrightarrow> 5 < x"
definition Q :: "nat \<Rightarrow> bool" where "Q x \<longleftrightarrow> 3 < x"
definition P2 :: "nat \<Rightarrow> bool" where "P2 x \<longleftrightarrow> 5 < x"

lemma PQ: "P x \<Longrightarrow> Q x" by (simp add: P_def Q_def)
lemma P_P2: "P x = P2 x" by (simp add: P_def P2_def)
lemma P2_6: "P2 6" by (simp add: P2_def)

ML \<open>
fun check name b = if b then () else error ("Failed check: " ^ name);

(*a failing check also shows what it got*)
fun check_showing name shown b =
  if b then () else error ("Failed check: " ^ name ^ "\n" ^ shown ());

fun plain ctxt t = Print_Mode.setmp [] (fn () => Syntax.string_of_term ctxt t) ();

fun read_prop ctxt = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_schematic ctxt);
fun read_term ctxt = Syntax.read_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt);

(*a theorem stating s, schematic variables allowed*)
fun mk_thm ctxt s = Skip_Proof.make_thm (Proof_Context.theory_of ctxt) (read_prop ctxt s);

(*s assumed, as the simplifier assumes a premise*)
fun assume_prop ctxt s = Thm.assume (Thm.cterm_of ctxt (Syntax.read_prop ctxt s));

fun eq_props (ts, us) = eq_list (op aconv) (ts, us);
fun eq_prop_sets (ts, us) = eq_set (op aconv) (ts, us);

fun check_props name ctxt (ts, ss) =
  check_showing name (fn () => commas (map (plain ctxt) ts))
    (eq_props (ts, map (read_prop ctxt) ss));

(*the rules the dispatch gives*)
fun rules ctxt th = map Thm.prop_of (#1 (Simplifier.mksimps_context th ctxt));

(*the rules the simpset holds after add_simps on a simpset without rules*)
fun simpset_rules ctxt ths =
  Simplifier.clear_simpset ctxt |> Simplifier.add_simps ths |> Simplifier.simpset_of
  |> Simplifier.dest_simps |> map (Thm.prop_of o #2);

fun handler_names ctxt = map #1 (#mksimps_handlers (Simplifier.dest_ss (Simplifier.simpset_of ctxt)));


(* call log *)

(*Calls are logged into a variable carried by the context, so that checks running in parallel
  theories do not share a log, and calls whose context changes are dropped are still seen.*)
structure Call_Log = Proof_Data
(
  type T = (string * thm) list Synchronized.var option;
  fun init _ = NONE;
);

fun log_call ctxt entry =
  (case Call_Log.get ctxt of
    SOME var => Synchronized.change var (cons entry)
  | NONE => ());

(*the calls logged while f runs on ctxt with a fresh log, in calling order*)
fun calls_of f ctxt =
  let
    val var = Synchronized.var "calls" [];
    val _ = f (Call_Log.put (SOME var) ctxt);
  in rev (Synchronized.value var) end;

fun call_names (calls: (string * thm) list) = map #1 calls;
fun call_props (calls: (string * thm) list) = map (Thm.prop_of o #2) calls;


(* handlers for the tests *)

(*registers a handler that logs (name, theorem) and then answers with result*)
fun add_handler name {patterns, priority, kept} result =
  Simplifier.add_mksimps_handler (name,
    Simplifier.make_mksimps_handler
     {patterns = patterns, priority = priority, kept_by_clear_simpset = kept,
      handler = fn ctxt => fn th => (log_call ctxt (name, th); result ctxt th)});

(*answers*)
fun pass _ _ = NONE;
fun default_rules ctxt th = SOME (Simplifier.get_mksimps_context ctxt th ctxt);
fun no_rules ctxt _ = SOME ([], ctxt);

(*the theorems recorded into the context, most recent first*)
structure Recorded = Proof_Data (type T = thm list fun init _ = []);

fun record_and_default_rules ctxt th = default_rules (Recorded.map (cons th) ctxt) th;

(*the calls during the dispatch of th*)
fun dispatch_calls ctxt th = calls_of (fn ctxt' => Simplifier.mksimps_context th ctxt') ctxt;
\<close>

end
