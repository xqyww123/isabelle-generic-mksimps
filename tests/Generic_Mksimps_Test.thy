(* Checks of mksimps handlers within one theory.  The numbers are those of section 6 of
   ai-artifacts/GENERIC_MKSIMPS_PLAN.md; merging is checked in Generic_Mksimps_Merge.  Any
   failing check fails the build. *)

theory Generic_Mksimps_Test
  imports Generic_Mksimps_Test_Base
begin

section \<open>Rules of Isabelle2026 without the feature\<close>

text \<open>Recorded with HOL's mksimps function on Isabelle2026 without the feature, from theorems made by
  \<open>mk_thm\<close>; each rule printed as a string that reads back to the recorded term.\<close>

ML \<open>
val baseline_hol =
 [("P a \<and> R b", ["P a \<equiv> True", "R b \<equiv> True"]),
  ("(P a \<and> R b) \<and> P (f a)", ["P a \<equiv> True", "R b \<equiv> True", "P (f a) \<equiv> True"]),
  ("\<forall>i. P (f i)", ["P (f ?x1) \<equiv> True"]),
  ("R b \<longrightarrow> P a", ["R b \<Longrightarrow> P a \<equiv> True"]),
  ("if C then P a else R b", ["C \<Longrightarrow> P a \<equiv> True", "\<not> C \<Longrightarrow> R b \<equiv> True"]),
  ("True", []),
  ("False", []),
  ("\<not> P a", ["P a \<equiv> False"]),
  ("a = b", ["a \<equiv> b"]),
  ("\<forall>x\<in>S. P x \<and> R x", ["?x2 \<in> S \<Longrightarrow> P ?x2 \<equiv> True", "?x2 \<in> S \<Longrightarrow> R ?x2 \<equiv> True"]),
  ("P ?x \<and> R ?y", ["P ?x2 \<equiv> True", "R ?y2 \<equiv> True"]),
  ("\<forall>i. P i \<longrightarrow> R i \<and> P (f i)",
    ["P ?x3 \<Longrightarrow> R ?x3 \<equiv> True", "P ?x3 \<Longrightarrow> P (f ?x3) \<equiv> True"]),
  ("(if C then g else h) a", ["(if C then g else h) a \<equiv> True"]),
  ("\<And>x. P x \<and> R x", ["P ?x2 \<equiv> True", "R ?x2 \<equiv> True"]),
  ("R a \<Longrightarrow> P a \<and> R b", ["R a \<Longrightarrow> P a \<equiv> True", "R a \<Longrightarrow> R b \<equiv> True"]),
  ("P a \<longrightarrow> R b \<and> P (f b)", ["P a \<Longrightarrow> R b \<equiv> True", "P a \<Longrightarrow> P (f b) \<equiv> True"]),
  ("(a::nat) \<equiv> b", ["(a::nat) \<equiv> b"]),
  ("(\<forall>i. P i) \<and> (\<forall>j. R j)", ["P ?x1 \<equiv> True", "R ?x1 \<equiv> True"]),
  ("\<forall>i j. P i \<and> R j", ["P ?x3 \<equiv> True", "R ?xa3 \<equiv> True"]),
  ("P ?x \<longrightarrow> R ?x", ["P ?x2 \<Longrightarrow> R ?x2 \<equiv> True"]),
  ("\<And>x. f x \<equiv> f a", ["f ?x \<equiv> f a"]),
  ("R a \<Longrightarrow> (a::nat) \<equiv> b", ["R a \<Longrightarrow> a \<equiv> b"])];

(*Pure's mksimps function keeps meta-equalities only*)
val baseline_pure =
  baseline_hol |> map (fn (input, _) =>
    (input,
      if input = "(a::nat) \<equiv> b" then ["(a::nat) \<equiv> b"]
      else if input = "R a \<Longrightarrow> (a::nat) \<equiv> b" then ["R a \<Longrightarrow> a \<equiv> b"]
      else []));

fun check_baseline name ctxt ctxt' =
  List.app (fn (input, expected) =>
    let val th = mk_thm ctxt input in
      check_props (name ^ ", mksimps_context: " ^ input) ctxt (rules ctxt' th, expected);
      check_props (name ^ ", mksimps: " ^ input) ctxt
        (map Thm.prop_of (Simplifier.mksimps ctxt' th), expected)
    end);

val hol_handler_names = ["HOL.All", "HOL.If", "HOL.conj", "HOL.implies"];
val without_hol_handlers = fold Simplifier.del_mksimps_handler hol_handler_names;
\<close>


section \<open>1. The table is empty\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val pure_empty = Simplifier.empty_simpset ctxt;
  val hol_slot_empty =
    pure_empty |> Simplifier.set_mksimps (Simpdata.mksimps Simpdata.mksimps_pairs);
in
  val _ = check "1: no handlers after empty_simpset" (null (handler_names pure_empty));
  val _ = check_baseline "1: Pure's empty simpset" ctxt pure_empty baseline_pure;
  val _ = check_baseline "1: empty simpset, HOL's mksimps function" ctxt hol_slot_empty baseline_hol;
end
\<close>


section \<open>HOL's connective handlers\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val handlers = #mksimps_handlers (Simplifier.dest_ss (Simplifier.simpset_of ctxt));
  fun first_prem th = hd (Thm.prems_of th);
  val expected =
   [("HOL.All", @{thm spec}), ("HOL.If", @{thm if_bool_eq_conj} RS @{thm iffD1}),
    ("HOL.conj", @{thm conjunct1}), ("HOL.implies", @{thm mp})];
  val shown =
    Print_Mode.setmp [] (fn () => Pretty.string_of (Simplifier.pretty_simpset false ctxt)) ();
in
  val _ = check "HOL: exactly the four handlers in Main" (map #1 handlers = hol_handler_names);
  val _ =
    expected |> List.app (fn (name, rl) =>
      check ("HOL: " ^ name)
        (case AList.lookup (op =) handlers name of
          SOME {patterns = [pattern], priority = 0, kept_by_clear_simpset = true} =>
            pattern aconv first_prem rl
        | _ => false));
  val _ = check "HOL: print_simpset shows the handlers"
    (String.isSubstring "mksimps handlers:" shown andalso
      String.isSubstring "HOL.conj:" shown andalso
      String.isSubstring "priority 0, kept_by_clear_simpset true" shown);
end
\<close>


section \<open>7. The same rules as without the feature\<close>

ML \<open>
local
  val ctxt = \<^context>;
in
  val _ = check_baseline "7: Main" ctxt ctxt baseline_hol;
  val _ =
    baseline_hol |> List.app (fn (input, _) =>
      let val th = mk_thm ctxt input in
        check ("7: the simplifier's own path: " ^ input)
          (eq_prop_sets (simpset_rules ctxt [th], simpset_rules (without_hol_handlers ctxt) [th]))
      end);
end
\<close>


section \<open>2. Premises and where their registrations can be used\<close>

text \<open>A handler on every proposition records each theorem it receives; a simproc on \<open>P _\<close> reports
  what it sees.  The expected firings are those of Isabelle2026 without the feature, with a
  mksimps function that records every theorem it receives and splits conjunctions.\<close>

ML \<open>
type firing =
 {at: term,
  records: (term * bool) list,  (*proposition, simproc_can_use_thm*)
  record_hyps: term list list,
  prems: term list,
  nested: (bool * bool) list,  (*simproc_can_use_thm after clear_simpset, then add_prems*)
  pair_a_c: bool option,  (*simproc_can_use_thm of the records P a, P c joined*)
  no_hyps: bool};

structure Firing_Log = Proof_Data
(
  type T = firing list Synchronized.var option;
  fun init _ = NONE;
);

val add_record_handler =
  add_handler "test.record" {patterns = [\<^prop>\<open>x\<close>], priority = ~10, kept = true}
    record_and_default_rules;

fun firing_of ctxt ct : firing =
  let
    val can = Simplifier.simproc_can_use_thm;
    val recorded = Recorded.get ctxt;
    val prems = Simplifier.prems_of ctxt;
    val nested_ctxt = Simplifier.clear_simpset ctxt;
    val nested_prems_ctxt = Simplifier.add_prems prems nested_ctxt;
    fun find t = find_first (fn r => Thm.prop_of r aconv t) recorded;
    val pair_a_c =
      (case (find \<^prop>\<open>P a\<close>, find \<^prop>\<open>P c\<close>) of
        (SOME ra, SOME rc) => SOME (can ctxt (Conjunction.intr ra rc))
      | _ => NONE);
  in
   {at = Thm.term_of ct,
    records = map (fn r => (Thm.prop_of r, can ctxt r)) recorded,
    record_hyps = map Thm.hyps_of recorded,
    prems = map Thm.prop_of prems,
    nested = map (fn r => (can nested_ctxt r, can nested_prems_ctxt r)) recorded,
    pair_a_c = pair_a_c,
    no_hyps = can ctxt @{thm TrueI}}
  end;

val report = Simplifier.make_simproc \<^context>
  {name = "report_P", kind = Simplifier.Simproc, lhss = [\<^term>\<open>P x\<close>], identifier = [],
   proc = fn _ => fn ctxt => fn ct =>
    ((case Firing_Log.get ctxt of
        SOME var => Synchronized.change var (cons (firing_of ctxt ct))
      | NONE => ());
     NONE)};

(*uses a recorded P x to rewrite Q x to True; checked: only if simproc_can_use_thm*)
fun uses_P checked = Simplifier.make_simproc \<^context>
  {name = "uses_P", kind = Simplifier.Simproc, lhss = [\<^term>\<open>Q x\<close>], identifier = [],
   proc = fn _ => fn ctxt => fn ct =>
    (case Thm.term_of ct of
      Const (\<^const_name>\<open>Q\<close>, _) $ x =>
        Recorded.get ctxt
        |> find_first (fn r =>
            Thm.prop_of r aconv HOLogic.mk_Trueprop (\<^Const>\<open>P\<close> $ x) andalso
            (not checked orelse Simplifier.simproc_can_use_thm ctxt r))
        |> Option.map (fn r => (r RS @{thm PQ}) RS @{thm Eq_TrueI})
    | _ => NONE)};

(*the firings and the result of rewriting s*)
fun observe ctxt conv procs simps s =
  let
    val var = Synchronized.var "firings" [];
    val ctxt' = ctxt
      |> Firing_Log.put (SOME var)
      |> add_record_handler
      |> fold Simplifier.add_proc (report :: procs)
      |> Simplifier.add_simps simps;
    val res = conv ctxt' (Thm.cterm_of ctxt (Syntax.read_prop ctxt s));
  in (rev (Synchronized.value var), res) end;

val mutual = Simplifier.asm_full_rewrite;
val sequential = Simplifier.asm_lr_rewrite;

(*expected: (at, [(record, usable)], prems_of) for each firing*)
fun check_firings name ctxt (firings: firing list, expected) =
  check name
    (eq_list (fn ({at, records, prems, ...}: firing, (at', records', prems')) =>
        at aconv read_term ctxt at' andalso
        eq_list (fn ((t, b), (s, b')) => t aconv read_prop ctxt s andalso b = b')
          (records, records') andalso
        eq_props (prems, map (read_prop ctxt) prems'))
      (firings, expected));

fun check_result name ctxt (res, rhs, hyps) =
  check name
    (Thm.term_of (Thm.rhs_of res) aconv read_prop ctxt rhs andalso
      eq_props (Thm.hyps_of res, map (read_prop ctxt) hyps));
\<close>

subsection \<open>The visibility table of section 4.4\<close>

ML \<open>
local
  val ctxt = \<^context>;
  fun firings conv s = #1 (observe ctxt conv [] [] s);
  val P_a_c_d = "P a \<Longrightarrow> P c \<Longrightarrow> P d";
in
  val _ = check_firings "2: mutual, P a simplified itself" ctxt
    (firings mutual "P a \<Longrightarrow> R d", [("P a", [("P a", false)], [])]);
  val _ = check_firings "2: mutual, P a rewritten to P b" ctxt
    (firings mutual "a = b \<Longrightarrow> P a \<Longrightarrow> R d",
      [("P b", [("P a", false), ("a = b", true)], ["a = b"])]);
  val _ = check_firings "2: mutual, P a and P c" ctxt
    (firings mutual "P a \<Longrightarrow> P c \<Longrightarrow> R d",
      [("P a", [("P c", true), ("P a", false)], ["P c"]),
       ("P c", [("P c", false), ("P a", true)], ["P a"])]);
  val _ = check_firings "2: mutual, P a and P c, conclusion" ctxt
    (firings mutual P_a_c_d,
      [("P a", [("P c", true), ("P a", false)], ["P c"]),
       ("P c", [("P c", false), ("P a", true)], ["P a"]),
       ("P d", [("P c", true), ("P a", true)], ["P a", "P c"])]);
  val _ = check_firings "2: sequential, P a simplified itself" ctxt
    (firings sequential "P a \<Longrightarrow> R d", [("P a", [], [])]);
  val _ = check_firings "2: sequential, P a rewritten to P b" ctxt
    (firings sequential "a = b \<Longrightarrow> P a \<Longrightarrow> R d", [("P b", [("a = b", true)], ["a = b"])]);
  val _ = check_firings "2: sequential, P a and P c, conclusion" ctxt
    (firings sequential P_a_c_d,
      [("P a", [], []),
       ("P c", [("P a", true)], ["P a"]),
       ("P d", [("P c", true), ("P a", true)], ["P c", "P a"])]);
  val _ =
    [("mutual", mutual), ("sequential", sequential)] |> List.app (fn (mode, conv) =>
      check_firings ("2: not visible outside the implication, " ^ mode) ctxt
        (firings conv "(P a \<longrightarrow> P b) \<and> P c",
          [("P a", [], []), ("P b", [("P a", true)], ["P a"]), ("P c", [], [])]));

  (*parts of a conjunction carry the whole conjunction as hypothesis*)
  val conj_firings = firings mutual "P a \<and> R b \<Longrightarrow> P c";
  val _ = check_firings "2: mutual, conjunction" ctxt
    (conj_firings,
      [("P a", [("R b", false), ("P a", false)], []),
       ("P c", [("R b", true), ("P a", true)], ["P a \<and> R b"])]);
  val _ = check "2: mutual, conjunction, hypotheses"
    (forall (fn {record_hyps, ...}: firing =>
        forall (fn hyps => eq_props (hyps, [\<^prop>\<open>P a \<and> R b\<close>])) record_hyps) conj_firings);
  val _ = check_firings "2: sequential, conjunction" ctxt
    (firings sequential "P a \<and> R b \<Longrightarrow> P c",
      [("P a", [], []), ("P c", [("R b", true), ("P a", true)], ["P a \<and> R b"])]);

  (*a theorem with two hypotheses; a theorem without hypotheses; nested simplification*)
  val mutual_firings = firings mutual P_a_c_d;
  val _ = check "2: two hypotheses"
    (map #pair_a_c mutual_firings = [SOME false, SOME false, SOME true]);
  val _ = check "2: no hypotheses" (forall #no_hyps mutual_firings);
  val _ = check "2: nested simplification"
    (#nested (List.last mutual_firings) = [(false, true), (false, true)]);
end
\<close>

subsection \<open>End to end: using a registration with and without the check\<close>

ML \<open>
local
  val ctxt = \<^context>;
  fun result conv checked simps s = #2 (observe ctxt conv [uses_P checked] simps s);
  val P_P2 = [@{thm P_P2}];
in
  val _ =
    [("mutual", mutual), ("sequential", sequential)] |> List.app (fn (mode, conv) =>
      [true, false] |> List.app (fn checked =>
        check_result ("2: usable in the conclusion, " ^ mode) ctxt
          (result conv checked [] "P a \<Longrightarrow> Q a", "True", [])));

  (*moment 1: the premise P a \<and> Q a is simplified while its parts are registered*)
  val _ = check_result "2: moment 1, mutual, unchecked" ctxt
    (result mutual false [] "P a \<and> Q a \<Longrightarrow> R d", "P a \<Longrightarrow> R d", ["P a \<and> Q a"]);
  val _ = check_result "2: moment 1, mutual, checked" ctxt
    (result mutual true [] "P a \<and> Q a \<Longrightarrow> R d", "P a \<and> Q a \<Longrightarrow> R d", []);
  val _ =
    [true, false] |> List.app (fn checked =>
      check_result "2: moment 1, sequential" ctxt
        (result sequential checked [] "P a \<and> Q a \<Longrightarrow> R d", "P a \<and> Q a \<Longrightarrow> R d", []));

  (*moment 2: the premise P a is rewritten to P2 a, its registration stays*)
  val _ = check_result "2: moment 2, mutual, unchecked" ctxt
    (result mutual false P_P2 "P a \<Longrightarrow> Q a", "True", ["P a"]);
  val _ = check_result "2: moment 2, mutual, checked" ctxt
    (result mutual true P_P2 "P a \<Longrightarrow> Q a", "P2 a \<Longrightarrow> Q a", []);
  val _ =
    [true, false] |> List.app (fn checked =>
      check_result "2: moment 2, sequential" ctxt
        (result sequential checked P_P2 "P a \<Longrightarrow> Q a", "P2 a \<Longrightarrow> Q a", []));

  (*the simp method fails on the hypothesis left behind*)
  fun prove checked s =
    Exn.capture (fn () =>
      Goal.prove (ctxt |> add_record_handler |> Simplifier.add_proc (uses_P checked)) [] []
        (Syntax.read_prop ctxt s) (fn {context, ...} => asm_full_simp_tac context 1)) ();
  val _ = check "2: unchecked: Undeclared hyps"
    (case prove false "P a \<and> Q a \<Longrightarrow> P a" of
      Exn.Exn (ERROR msg) => String.isSubstring "Undeclared hyps" msg
    | _ => false);
  val _ = check "2: checked: proved"
    (case prove true "P a \<and> Q a \<Longrightarrow> P a" of Exn.Res _ => true | _ => false);
end
\<close>


section \<open>4. The theorem a handler gets has exact maxidx\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val logged =
    ctxt |> add_handler "test.maxidx" {patterns = [\<^prop>\<open>P x\<close>], priority = 5, kept = true}
      default_rules;
  (*the handler of the concept example in section 4.6*)
  fun concept_like ctxt th =
    if Thm.nprems_of th > 0 orelse Thm.maxidx_of th >= 0 then NONE
    else record_and_default_rules ctxt th;
  val concept =
    ctxt |> add_handler "test.concept" {patterns = [\<^prop>\<open>P x\<close>], priority = 5, kept = true}
      concept_like;
  fun recorded s =
    map Thm.prop_of (Recorded.get (#2 (Simplifier.mksimps_context (assume_prop ctxt s) concept)));
in
  val _ = check "4: P a from the assumed P a \<and> R b"
    (case dispatch_calls logged (assume_prop ctxt "P a \<and> R b") of
      [(_, th)] => Thm.prop_of th aconv \<^prop>\<open>P a\<close> andalso Thm.maxidx_of th = ~1
    | _ => false);
  val _ = check_props "4: concept example, P a \<and> R b" ctxt
    (recorded "P a \<and> R b", ["P a"]);
  val _ = check_props "4: concept example, (P a \<and> R b) \<and> P c" ctxt
    (recorded "(P a \<and> R b) \<and> P c", ["P c", "P a"]);
end
\<close>


section \<open>5. Patterns are generalised when registered\<close>

ML \<open>
local
  val ctxt =
    \<^context> |> add_handler "test.finite" {patterns = [\<^prop>\<open>finite A\<close>], priority = 5, kept = true}
      pass;
  fun called ctxt th = not (null (dispatch_calls ctxt th));
  val poly = mk_thm ctxt "finite (?A :: ?'c set)";

  val ([_], ctxt_x) = Variable.add_fixes ["x"] \<^context>;
  val P_x = Syntax.read_prop ctxt_x "P x";
  val fixed =
    ctxt_x |> add_handler "test.fixed" {patterns = [P_x], priority = 5, kept = true} pass;
in
  val _ = check "5: stored pattern"
    (case AList.lookup (op =) (#mksimps_handlers (Simplifier.dest_ss (Simplifier.simpset_of ctxt)))
        "test.finite" of
      SOME {patterns = [pattern], ...} => pattern aconv read_prop ctxt "finite (?A :: ?'a set)"
    | _ => false);
  val _ = check "5: nat set" (called ctxt (assume_prop ctxt "finite (S :: nat set)"));
  val _ = check "5: another type variable" (called ctxt (assume_prop ctxt "finite (T :: 'b set)"));
  val _ = check "5: polymorphic simp rule" (called ctxt poly);
  val _ = check "5: polymorphic simp rule, add_simps"
    (not (null (calls_of (fn ctxt' => simpset_rules ctxt' [poly]) ctxt)));
  val _ = check "5: fixed variable, same" (called fixed (Thm.assume (Thm.cterm_of fixed P_x)));
  val _ = check "5: fixed variable, other" (not (called fixed (assume_prop fixed "P a")));
end
\<close>


section \<open>3. A handler returning SOME gives all rules of the theorem\<close>

ML \<open>
local
  val ctxt = \<^context>;
  fun with_answer answer =
    ctxt |> add_handler "test.all" {patterns = [\<^prop>\<open>P x\<close>], priority = 5, kept = true} answer;
  val P_a = assume_prop ctxt "P a";
  val P_a_eq = read_prop ctxt "P a \<equiv> True";
  fun in_simpset answer = member (op aconv) (simpset_rules (with_answer answer) [mk_thm ctxt "P a"]) P_a_eq;
in
  val _ = check_props "3: SOME []" ctxt (rules (with_answer no_rules) P_a, []);
  val _ = check_props "3: SOME [] in a conjunction" ctxt
    (rules (with_answer no_rules) (assume_prop ctxt "P a \<and> R b"), ["R b \<equiv> True"]);
  val _ = check "3: SOME [], simplifier's path" (not (in_simpset no_rules));
  val _ = check_props "3: SOME default rules" ctxt (rules (with_answer default_rules) P_a, ["P a \<equiv> True"]);
  val _ = check "3: SOME default rules, simplifier's path" (in_simpset default_rules);
  val _ = check_props "3: NONE" ctxt (rules (with_answer pass) P_a, ["P a \<equiv> True"]);
  val _ = check "3: NONE, simplifier's path" (in_simpset pass);
end
\<close>


section \<open>6. Recursion through HOL's connective handlers\<close>

ML \<open>
val recursion_inputs =
 [("P a \<and> R b", ["P a"]),
  ("(P a \<and> R b) \<and> P c", ["P a", "P c"]),
  ("\<forall>i. P (f i)", ["P (f ?x1)"]),
  ("R b \<longrightarrow> P a", ["R b \<Longrightarrow> P a"]),
  ("if C then P a else R b", ["C \<Longrightarrow> P a"])];

fun received ctxt s = call_props (dispatch_calls ctxt (assume_prop ctxt s));

local
  val ctxt =
    \<^context> |> add_handler "test.rec" {patterns = [\<^prop>\<open>P x\<close>], priority = 5, kept = true}
      record_and_default_rules;
in
  val _ =
    recursion_inputs |> List.app (fn (s, expected) =>
      check_props ("6: " ^ s) ctxt (received ctxt s, expected));
  val _ = check_props "6: the context goes along the recursion" ctxt
    (map Thm.prop_of
      (Recorded.get (#2 (Simplifier.mksimps_context (assume_prop ctxt "(P a \<and> R b) \<and> P c") ctxt))),
     ["P c", "P a"]);
  val _ =
    recursion_inputs |> List.app (fn (s, _) =>
      check ("6: without HOL's handlers: " ^ s) (null (received (without_hol_handlers ctxt) s)));
end
\<close>


section \<open>8. Meta-forall and premises\<close>

ML \<open>
local
  val ctxt =
    \<^context> |> add_handler "test.prem" {patterns = [\<^prop>\<open>P x\<close>], priority = 5, kept = true}
      default_rules;
  val empty =
    Simplifier.empty_simpset \<^context>
    |> add_handler "test.unrelated" {patterns = [\<^prop>\<open>P x\<close>], priority = 5, kept = true} pass;
in
  val _ = check_props "8: assumed \<And>y. R y \<Longrightarrow> P y" ctxt
    (call_props (dispatch_calls ctxt (assume_prop ctxt "\<And>y. R y \<Longrightarrow> P y")), ["R ?y \<Longrightarrow> P ?y"]);
  val _ = check_props "8: simp rule with a premise" ctxt
    (call_props (calls_of (fn ctxt' => simpset_rules ctxt' [mk_thm ctxt "R ?y \<Longrightarrow> P ?y"]) ctxt),
     ["R ?y \<Longrightarrow> P ?y"]);
  val _ = check_props "8: Pure's mksimps function gets the theorem without gen_all" ctxt
    (rules empty (mk_thm ctxt "\<And>x. f x \<equiv> f a"), []);
end
\<close>


section \<open>9. Explicit simp rules\<close>

ML \<open>
local
  val ctxt =
    \<^context> |> add_handler "test.explicit" {patterns = [\<^prop>\<open>P x\<close>], priority = 5, kept = true}
      record_and_default_rules;
  val th = mk_thm ctxt "P a";
  val added = Simplifier.add_simps [th] ctxt;
  fun has_rule ctxt' =
    member (op aconv) (map (Thm.prop_of o #2) (Simplifier.dest_simps (Simplifier.simpset_of ctxt')))
      (read_prop ctxt "P a \<equiv> True");
in
  val _ = check "9: called"
    (call_names (calls_of (fn ctxt' => Simplifier.add_simps [th] ctxt') ctxt) = ["test.explicit"]);
  val _ = check "9: rule added" (has_rule added);
  val _ = check "9: context changes dropped" (null (Recorded.get added));
  val _ = check "9: del_simps removes the same rules" (not (has_rule (Simplifier.del_simps [th] added)));
end
\<close>


section \<open>10. Setting the mksimps function keeps the handlers\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val reset = Simplifier.set_mksimps (Simpdata.mksimps Simpdata.mksimps_pairs);
  val handler =
    ctxt |> add_handler "test.kept" {patterns = [\<^prop>\<open>P x\<close>], priority = 5, kept = true} pass;
  fun wrap ctxt' =
    let val mk = Simplifier.get_mksimps_context ctxt'
    in Simplifier.set_mksimps_context (fn th => fn ctxt'' => (log_call ctxt'' ("wrapper", th); mk th ctxt'')) ctxt' end;
  fun calls ctxt' = call_names (dispatch_calls ctxt' (assume_prop ctxt "P a"));
in
  val _ = check "10: handler after set_mksimps" (calls (reset handler) = ["test.kept"]);
  val _ = check "10: wrapped mksimps function" (calls (wrap ctxt) = ["wrapper"]);
  val _ = check "10: wrapped mksimps function after set_mksimps" (null (calls (reset (wrap ctxt))));
end
\<close>


section \<open>12. Option and priority\<close>

ML \<open>
local
  val ctxt = \<^context>;
  val P_x = [\<^prop>\<open>P x\<close>];
  fun add name priority = add_handler name {patterns = P_x, priority = priority, kept = true};
  fun calls ctxt' s = call_names (dispatch_calls ctxt' (assume_prop ctxt s));
  val first_some =
    ctxt |> add "test.hi" 10 pass |> add "test.mid" 0 default_rules |> add "test.lo" ~10 default_rules;
  val all_none = ctxt |> add "test.n1" 1 pass |> add "test.n2" 0 pass;
  val same_priority = ctxt |> add "test.b" 0 pass |> add "test.a" 0 pass;
  val around_conj = ctxt
    |> add_handler "test.conj_pre" {patterns = [\<^prop>\<open>x \<and> y\<close>], priority = 1, kept = true} pass
    |> add_handler "test.conj_post" {patterns = [\<^prop>\<open>x \<and> y\<close>], priority = ~1, kept = true} pass;
  val two_patterns = ctxt
    |> add_handler "test.two" {patterns = [\<^prop>\<open>P x\<close>, \<^prop>\<open>P (f y)\<close>], priority = 0, kept = true}
      pass;
in
  val _ = check "12: by priority, until SOME" (calls first_some "P a" = ["test.hi", "test.mid"]);
  val _ = check "12: all NONE" (calls all_none "P a" = ["test.n1", "test.n2"]);
  val _ = check_props "12: all NONE, mksimps function" ctxt
    (rules all_none (assume_prop ctxt "P a"), ["P a \<equiv> True"]);
  val _ = check "12: same priority, by name" (calls same_priority "P a" = ["test.a", "test.b"]);
  val _ = check "12: before and after HOL.conj" (calls around_conj "P a \<and> R b" = ["test.conj_pre"]);
  val _ = check_props "12: HOL.conj after a NONE" ctxt
    (rules around_conj (assume_prop ctxt "P a \<and> R b"), ["P a \<equiv> True", "R b \<equiv> True"]);
  val _ = check "12: two matching patterns, one call" (calls two_patterns "P (f a)" = ["test.two"]);
end
\<close>


section \<open>13. Names\<close>

ML \<open>
local
  val ctxt = \<^context>;
  fun calls ctxt' s = call_names (dispatch_calls ctxt' (assume_prop ctxt s));
  val replaced = ctxt
    |> add_handler "test.n" {patterns = [\<^prop>\<open>P x\<close>], priority = 0, kept = true} pass
    |> add_handler "test.n" {patterns = [\<^prop>\<open>R x\<close>], priority = 0, kept = true} pass;
  val deleted = Simplifier.del_mksimps_handler "test.n" replaced;
  val absent =
    deleted |> Context_Position.set_visible false |> Simplifier.del_mksimps_handler "test.absent";
in
  val _ = check "13: replaced, old pattern" (null (calls replaced "P a"));
  val _ = check "13: replaced, new pattern" (calls replaced "R a" = ["test.n"]);
  val _ = check "13: deleted" (null (calls deleted "R a"));
  val _ = check "13: deleted, listing" (not (member (op =) (handler_names deleted) "test.n"));
  val _ = check "13: deleting an absent name" (handler_names absent = handler_names deleted);
end
\<close>


section \<open>14. Clearing\<close>

ML \<open>
fun method_tac ctxt s =
  let val (text, _) = Method.read_closure_input ctxt (Input.string s)
  in NO_CONTEXT_TACTIC ctxt (Method.evaluate text ctxt []) end;

local
  val ctxt = \<^context>
    |> add_handler "test.kept" {patterns = [\<^prop>\<open>P x\<close>], priority = 0, kept = true} default_rules
    |> add_handler "test.dropped" {patterns = [\<^prop>\<open>P x\<close>], priority = 1, kept = false} pass;
  val cleared = Simplifier.clear_simpset ctxt;
  val emptied = Simplifier.empty_simpset ctxt;
  fun calls ctxt' s = call_names (dispatch_calls ctxt' (assume_prop ctxt s));
  val simp_only_calls =
    calls_of (fn ctxt' =>
      Goal.prove ctxt' [] [] (Syntax.read_prop ctxt "P a \<and> R b \<Longrightarrow> P a")
        (fn {context, ...} => method_tac context "simp only:")) ctxt;
in
  val _ = check "14: empty_simpset, no handlers" (null (handler_names emptied));
  val _ = check "14: empty_simpset, none called" (null (calls emptied "P a \<and> R b"));
  val _ = check_props "14: empty_simpset, Pure's mksimps function" ctxt
    (rules emptied (assume_prop ctxt "P a \<and> R b"), []);
  val _ = check "14: clear_simpset keeps the flagged handlers"
    (eq_set (op =) (handler_names cleared, "test.kept" :: hol_handler_names));
  val _ = check "14: before clear_simpset" (calls ctxt "P a" = ["test.dropped", "test.kept"]);
  val _ = check "14: after clear_simpset" (calls cleared "P a" = ["test.kept"]);
  val _ =
    recursion_inputs |> List.app (fn (s, expected) =>
      check_props ("14: clear_simpset, recursion: " ^ s) ctxt (received cleared s, expected));
  val _ = check "14: simp only:"
    (not (null simp_only_calls) andalso
      forall (fn (name, th) => name = "test.kept" andalso Thm.prop_of th aconv \<^prop>\<open>P a\<close>)
        simp_only_calls);
end
\<close>

text \<open>The \<open>simplified\<close> attribute with arguments uses \<open>clear_simpset\<close> on the theory's simpset.\<close>

ML \<open>val simplified_calls = Synchronized.var "simplified" ([]: string list)\<close>

setup \<open>
  Simplifier.map_theory_simpset
   (fold (fn (name, kept) =>
      Simplifier.add_mksimps_handler (name,
        Simplifier.make_mksimps_handler
         {patterns = [\<^prop>\<open>P2 x\<close>], priority = 0, kept_by_clear_simpset = kept,
          handler = fn _ => fn _ => (Synchronized.change simplified_calls (cons name); NONE)}))
    [("test.simplified_kept", true), ("test.simplified_dropped", false)])
\<close>

lemmas test_simplified = TrueI[simplified P2_6]

setup \<open>
  Simplifier.map_theory_simpset
    (fold Simplifier.del_mksimps_handler ["test.simplified_kept", "test.simplified_dropped"])
\<close>

ML \<open>
val _ = check "14: simplified with arguments"
  (let val names = Synchronized.value simplified_calls
   in not (null names) andalso forall (fn name => name = "test.simplified_kept") names end);
\<close>


section \<open>15. Premises with schematic variables are not dispatched\<close>

ML \<open>
local
  val ctxt =
    \<^context> |> add_handler "test.schematic" {patterns = [\<^prop>\<open>P x\<close>], priority = 0, kept = true}
      pass;
in
  val _ = check "15: not called"
    (null (calls_of (fn ctxt' =>
      Simplifier.asm_full_rewrite ctxt' (Thm.cterm_of ctxt (read_prop ctxt "P ?z \<Longrightarrow> R d"))) ctxt));
end
\<close>


section \<open>16. mksimps goes through the dispatch\<close>

ML \<open>
local
  val ctxt =
    \<^context> |> add_handler "test.none" {patterns = [\<^prop>\<open>P x\<close>], priority = 0, kept = true}
      no_rules;
in
  val _ = check "16: mksimps" (null (Simplifier.mksimps ctxt (mk_thm ctxt "P a")));
end
\<close>

end
