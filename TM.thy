section\<open>A Theory of Turing Machines\<close>

theory TM
  imports Main
    "Supplementary/Lists" "Supplementary/Option_S"
    "Intro_Dest_Elim.IHOL_IDE"
begin


subsection\<open>Prerequisites\<close>

text\<open>We introduce the locale \<open>TM_abbrevs\<close> to scope local abbreviations.
  This allows easy access to notation without introducing possible bloat on the global scope.
  In other words, users of this theory have to \<^emph>\<open>opt-in\<close> to more specialized abbreviations.
  The idea for this is from the Style Guide for Contributors to IsarMathLib\<^footnote>\<open>\<^url>\<open>https://www.nongnu.org/isarmathlib/IsarMathLib/CONTRIBUTING.html\<close>\<close>.\<close>
locale TM_abbrevs

(* TODO consider extracting these to some other theory *)
type_synonym ('symbol) word = "'symbol list" (* TODO it seems "word" is not actually used anywhere. use or remove. *)


subsubsection\<open>Symbols\<close>

text\<open>Symbols on the tape are represented by \<^typ>\<open>'symbol option\<close>,
  where \<^const>\<open>None\<close> represents a \<^emph>\<open>blank\<close> tape-cell.
  This enables clear distinction between the symbols used by TM computations and those for TM inputs.
  Allowing TM input terms to contain \<^emph>\<open>blanks\<close> makes reasoning about TM computations harder,
  since TMs could not reasonably distinguish between the end of the input
  and a sequence of blanks as part of the input.\<close>

type_synonym ('symbol) tp_symbol = "'symbol option"
abbreviation (input) blank_symbol :: "('symbol) tp_symbol" where "blank_symbol \<equiv> None"
abbreviation (in TM_abbrevs) "Bk \<equiv> blank_symbol"
(* TODO consider notation, for instance "\<box>" ("#" is possible, but annoying, as it is used for lists) *)

text\<open>In the following, we will also refer to the type of symbols (\<^typ>\<open>'symbol\<close> here)
  with the short form \<^typ>\<open>'s\<close>.\<close>


subsubsection\<open>Tape Head Movement\<close>

text\<open>We define TM tape head moves as either shifting the TM head one cell (\<open>Shift_Left\<close> or \<open>Shift_Right\<close>),
  or doing nothing.
  \<open>No_Shift\<close> seems redundant, since for single-tape TMs it can be simulated by moving the head back-and-forth
  or just leaving out any step that performs \<open>No_Shift\<close> (integrate into the preceding step).
  However, for multi-tape TMs, these simple replacements do not work.

  \<^emph>\<open>Moving the TM head\<close> is equivalent to shifting the entire tape under the head.
  This is how we implement the head movement.\<close>

datatype head_move = Shift_Left | Shift_Right | No_Shift

(* consider introducing a type of actions:
 * type_synonym (in TM_abbrevs) ('s) action = "'s tp_symbol \<times> head_move" *)

subsection\<open>Turing Machines\<close>

text\<open>We model a (deterministic \<open>k\<close>-tape) TM over the type \<^typ>\<open>'q\<close> of states
  and the finite type \<^typ>\<open>'s\<close> of symbols, as a tuple of:\<close>

(* the inclusion of accepting states at this point seems somewhat arbitrary.
 * consider applying the "labelling" pattern used by @{cite forsterCoqTM2020},
 * as this would allow more advanced extensions, such as oracles as well *)

(* TODO define equality for TMs. regular equality is not really what we want
        (as the behavior of the transition functions outside of their intended range are irrelevant).
        possible solutions include defining TMs as quotient type with suitable equality function,
        and using relations instead of functions. this would be reusable for defining NTMs as well. *)

record ('q, 's) TM_record =
  tape_count :: nat \<comment> \<open>\<open>k\<close>, the number of tapes\<close>
  symbols :: "'s set" \<comment> \<open>\<open>\<Sigma>\<close>, the set of symbols, not including the \<^const>\<open>blank_symbol\<close>\<close>
  states :: "'q set" \<comment> \<open>\<open>Q\<close>, the set of states\<close>
  initial_state :: 'q \<comment> \<open>\<open>q\<^sub>0 \<in> Q\<close>, the initial state; computation will start on \<open>k\<close> blank tapes in this state\<close>
  final_states :: "'q set" \<comment> \<open>\<open>F \<subseteq> Q\<close>, the set of final states; if a TM is in a final state,
    its computation is considered finished (the TM has halted) and no further steps will be executed\<close>
  accepting_states :: "'q set" \<comment> \<open>\<open>F\<^sup>+ \<subseteq> F\<close>, the set of accepting states; if a TM halts in an accepting state,
    it is considered to have accepted the input\<close>

  next_state :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> 'q" \<comment> \<open>Maps the current state and vector of read symbols to the next state.\<close>
  next_write :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> nat \<Rightarrow> 's tp_symbol" \<comment> \<open>Maps the current state, read symbols and tape index
    to the symbol to write before transitioning to the next state.\<close>
  next_move  :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> nat \<Rightarrow> head_move" \<comment> \<open>Maps the current state, read symbols and tape index
    to the head movement to perform before transitioning to the next state.\<close>

abbreviation "TM k \<Sigma> Q q\<^sub>0 F F\<^sub>A \<delta>\<^sub>q \<delta>\<^sub>w \<delta>\<^sub>m \<equiv> \<lparr> TM_record.tape_count = k, symbols = \<Sigma>,
    states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sub>A,
    next_state = \<delta>\<^sub>q, next_write = \<delta>\<^sub>w, next_move = \<delta>\<^sub>m \<rparr>"

text\<open>The elements of type \<^typ>\<open>'s\<close> comprise the TM's input alphabet,
  and the wrapper \<^typ>\<open>'s tp_symbol\<close> represent its working alphabet, including the \<^const>\<open>blank_symbol\<close>.

  We split the transition function \<open>\<delta>\<close> into three components for easier access and definition.
  To perform an execution step, assuming that \<open>q :: 'q\<close> is the current state, and \<open>hds :: 's tp_symbol list\<close>
  are the symbols currently under the tape heads (the read symbols),
  each tape head first writes a symbol to its current position on the tape, then moves by one symbol to the left or right (or stays still).
  That is, the head on the \<open>i\<close>-th tape writes \<^term>\<open>next_write q hds i\<close>, then moves according to \<^term>\<open>next_move q hds i\<close>.
  After all head have performed their respective actions, \<open>next_state q hds\<close> is assigned as the new current state.\<close>

(* TODO update this *)
text\<open>
  As Isabelle does not provide dependent types, the transition function is not actually defined
  for vectors/tuples, but lists instead.
  As a result, the returned lists are not guaranteed to have \<open>k\<close> elements, as required.
  To avoid complex requirements for this function, we apply a trick similar to one used by Xu et. al.:
  invalid return values are ignored. Elements beyond the \<open>k\<close>-th will not be considered,
  and missing actions will be assumed to have no effect (write the same symbol that was read, do not move head).\<close>


paragraph\<open>Tape Symbols\<close>

(* TODO document *)
abbreviation tape_symbols_rec :: "('q, 's) TM_record \<Rightarrow> 's tp_symbol set"
  where "tape_symbols_rec M_rec \<equiv> options (symbols M_rec)"


paragraph\<open>Well-formed\<close>

text\<open>A vector \<open>hds\<close> of symbols currently under the TM-heads,
  is considered a well-formed state w.r.t. a TM \<open>M\<close>,
  iff the number of elements of \<open>hds\<close> matches the number of tapes of \<open>M\<close>,
  and all elements are valid symbols for \<open>M\<close>.\<close>

definition wf_hds_rec :: "('q, 's) TM_record \<Rightarrow> 's tp_symbol list \<Rightarrow> bool"
  where "wf_hds_rec M_rec hds \<equiv> length hds = tape_count M_rec \<and> set hds \<subseteq> tape_symbols_rec M_rec"

lemma wf_hds_rec_simps[simp]: "wf_hds_rec \<lparr>
    TM_record.tape_count = k, symbols = \<Sigma>,
    states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sub>A,
    next_state = \<delta>\<^sub>q, next_write = \<delta>\<^sub>w, next_move = \<delta>\<^sub>m
  \<rparr> hds \<longleftrightarrow> length hds = k \<and> set hds \<subseteq> options \<Sigma>"
  unfolding wf_hds_rec_def by simp

mk_ide wf_hds_rec_def |intro wf_hds_recI[intro]| |elim wf_hds_recE[elim]| |dest wf_hds_recD[dest]|


subsubsection\<open>A Type of Turing Machines\<close>

text\<open>To use TMs conveniently, we setup a type and a locale as follows:

  \<^item> We have defined the structure of TMs as a record.
  \<^item> We define our validity predicate over \<open>TM_record\<close> as a locale, as this allows more convenient access to the axioms.
  \<^item> From the predicate, a type of (valid) TMs is defined.
  \<^item> Using the type, we set up definitions and lemmas concerning TMs within a locale.
    The locale allows convenient access to the internals of TMs.

  A simpler form of this pattern has been used to define the type of filters (\<^typ>\<open>'a filter\<close>).\<close>

locale valid_TM_not_uniq =
  fixes M :: "('q, 's) TM_record"
  assumes at_least_one_tape: "tape_count M > 0" (* TODO motivate this assm. "why is this necessary?" edit: initial_config would have to be defined differently *)
    and symbol_axioms: "finite (symbols M)" "symbols M \<noteq> {}"
    and state_axioms: "finite (states M)" "initial_state M \<in> states M"
      "final_states M \<subseteq> states M" "accepting_states M \<subseteq> final_states M"
    and next_state_valid: "\<And>q hds. q \<in> states M \<Longrightarrow> wf_hds_rec M hds \<Longrightarrow> next_state M q hds \<in> states M"
    and next_write_valid: "\<And>q hds i. q \<in> states M \<Longrightarrow> wf_hds_rec M hds \<Longrightarrow> i < tape_count M \<Longrightarrow>
          next_write M q hds i \<in> tape_symbols_rec M"
begin
lemmas axioms = at_least_one_tape symbol_axioms state_axioms next_state_valid next_write_valid
end

locale valid_TM = valid_TM_not_uniq +
  \<comment> \<open>Require canonical default values for the transition function outside its intended definition range.
      There are two simple options for choosing default values:

      \<^bold>\<open>Canonical values\<close>. Use values that are always available in the context of TMs.
      This would result in the initial state \<open>q\<^sub>0\<close>, the \<open>blank_symbol\<close> and \<open>No_Shift\<close>.

      \<^bold>\<open>No-Op\<close>. Simply output the respective input value.
      Semantically, this relates to the TM looping endlessly in a constant configuration.
      This approach is somewhat problematic for \<open>next_write\<close>, as \<open>hds ! i\<close> is not defined for all values.
      This means that all functions will have to be defined with exactly \<open>hds ! i\<close> for out-of-bounds inputs,
      as it is the only value for which equality can be shown in Isabelle.

      We choose the second approach as we suspect it will integrate better with simple definitions.\<close>
  assumes next_state_default: "\<And>q hds. q \<notin> states M \<Longrightarrow> next_state M q hds = q"
    "\<And>q hds. \<not> wf_hds_rec M hds \<Longrightarrow> next_state M q hds = q"
    and next_write_default:   "\<And>q hds i. q \<notin> states M \<Longrightarrow> next_write M q hds i = hds ! i" (* TODO evaluate if this works out. should make things a bit easier, but could lead to unprovable goals *)
    "\<And>q hds i. \<not> wf_hds_rec M hds \<Longrightarrow> next_write M q hds i = hds ! i"
    "\<And>q hds i. \<not> i < tape_count M \<Longrightarrow> next_write M q hds i = hds ! i"
    and next_move_default:    "\<And>q hds i. q \<notin> states M \<Longrightarrow> next_move M q hds i = No_Shift"
    "\<And>q hds i. \<not> wf_hds_rec M hds \<Longrightarrow> next_move M q hds i = No_Shift"
    "\<And>q hds i. \<not> i < tape_count M \<Longrightarrow> next_move M q hds i = No_Shift"


lemma "wf_hds_rec M hds \<Longrightarrow> i < tape_count M \<Longrightarrow> hds ! i \<in> tape_symbols_rec M" by force

definition next_fun_wrapper :: "['x, nat, 's set, 'q set, 'q \<Rightarrow> 's option list \<Rightarrow> nat \<Rightarrow> 'x, 'q, 's option list, nat] \<Rightarrow> 'x"
  where "next_fun_wrapper default_val k \<Sigma> Q f q hds i \<equiv> if q \<in> Q \<and> length hds = k \<and> set hds \<subseteq> options \<Sigma> \<and> i < k then f q hds i else default_val"

abbreviation next_state_wrapper :: "[nat, 's set, 'q set, 'q \<Rightarrow> 's option list \<Rightarrow> 'q, 'q, 's option list] \<Rightarrow> 'q"
  where "next_state_wrapper k \<Sigma> Q f q hds \<equiv> next_fun_wrapper q k \<Sigma> Q (\<lambda>q hds i. f q hds) q hds 0"
abbreviation next_write_wrapper :: "[nat, 's set, 'q set, 'q \<Rightarrow> 's option list \<Rightarrow> nat \<Rightarrow> 's option, 'q, 's option list, nat] \<Rightarrow> 's option"
  where "next_write_wrapper k \<Sigma> Q f q hds i \<equiv> next_fun_wrapper (hds ! i) k \<Sigma> Q f q hds i"
abbreviation next_move_wrapper :: "[nat, 's set, 'q set, 'q \<Rightarrow> 's option list \<Rightarrow> nat \<Rightarrow> head_move, 'q, 's option list, nat] \<Rightarrow> head_move"
  where "next_move_wrapper k \<Sigma> Q f q hds i \<equiv> next_fun_wrapper No_Shift k \<Sigma> Q f q hds i"

lemma next_fun_wrapper_default[simp]:
  fixes k \<Sigma> Q f val and M :: "('q, 's) TM_record"
  defines "f' \<equiv> next_fun_wrapper val k \<Sigma> Q f"
  defines "f'' \<equiv> next_fun_wrapper val (tape_count M) (symbols M) (states M) f"
  shows "q \<notin> Q \<Longrightarrow> f' q hds i = val"
    and "length hds \<noteq> k \<Longrightarrow> f' q hds i = val"
    and "\<not> set hds \<subseteq> options \<Sigma> \<Longrightarrow> f' q hds i = val"
    and "\<not> i < k \<Longrightarrow> f' q hds i = val"
    and "\<not> wf_hds_rec M hds \<Longrightarrow> f'' q hds i = val"
  unfolding assms next_fun_wrapper_def by (blast intro!: if_not_P)+

lemma next_fun_wrapper_simps[simp]:
  fixes k \<Sigma> Q f val and M :: "('q, 's) TM_record"
  defines "f' \<equiv> next_fun_wrapper val k \<Sigma> Q f"
  defines "f'' \<equiv> next_fun_wrapper val (tape_count M) (symbols M) (states M) f"
  shows "q \<in> Q \<Longrightarrow> length hds = k \<Longrightarrow> set hds \<subseteq> options \<Sigma> \<Longrightarrow> i < k \<Longrightarrow> f' q hds i = f q hds i"
    and "q \<in> states M \<Longrightarrow> wf_hds_rec M hds \<Longrightarrow> i < tape_count M \<Longrightarrow> f'' q hds i = f q hds i"
  unfolding assms next_fun_wrapper_def using assms(2-) by (blast intro!: if_P)+

lemma next_state_wrapper_simps[simp]:
  fixes k \<Sigma> Q f val
  defines "f' \<equiv> next_fun_wrapper val k \<Sigma> Q f"
  assumes "q \<in> Q" and "length hds = k" and "set hds \<subseteq> options \<Sigma>"
  shows "k > 0 =simp=> f' q hds 0 = f q hds 0"
  using assms unfolding f'_def by (intro simp_impliesI, subst next_fun_wrapper_simps) fastforce+


definition TM_default_wrapper :: "('q, 's) TM_record \<Rightarrow> ('q, 's) TM_record"
  where "TM_default_wrapper M \<equiv> M\<lparr>
    next_state := next_state_wrapper (tape_count M) (symbols M) (states M) (next_state M),
    next_write := next_write_wrapper (tape_count M) (symbols M) (states M) (next_write M),
    next_move := next_move_wrapper (tape_count M) (symbols M) (states M) (next_move M)
  \<rparr>"

lemma TM_default_wrapper_simps[simp]:
  fixes M :: "('q, 's) TM_record"
  defines "M' \<equiv> TM_default_wrapper M"
  shows "tape_count M' = tape_count M"
    and "symbols M' = symbols M"
    and "states M' = states M"
    and "initial_state M' = initial_state M"
    and "final_states M' = final_states M"
    and "accepting_states M' = accepting_states M"
    and "next_state M' = next_state_wrapper (tape_count M) (symbols M) (states M) (next_state M)"
    and "next_write M' = next_write_wrapper (tape_count M) (symbols M) (states M) (next_write M)"
    and "next_move M' = next_move_wrapper (tape_count M) (symbols M) (states M) (next_move M)"
    and "wf_hds_rec M' = wf_hds_rec M"
  unfolding M'_def TM_default_wrapper_def by (induction M) force+

text\<open>Notes on assumptions.
  Many of these assumptions would be trivial to satisfy when explicitly constructing a TM,
  especially the premises of \<open>next_state_valid\<close> and \<open>next_write_valid\<close>.
  They are, however, very useful when constructing TMs from other TMs.\<close>


lemma valid_TM_wrapper[simp]: "valid_TM (TM_default_wrapper M) \<longleftrightarrow> valid_TM_not_uniq M"
  (is "valid_TM ?M' \<longleftrightarrow> _")
proof -
  note * = TM_default_wrapper_simps next_fun_wrapper_simps
  have h1: "valid_TM_axioms ?M'"
    using next_fun_wrapper_default
    by (unfold_locales, unfold *)
  have h2: "valid_TM_not_uniq ?M'" if "valid_TM_not_uniq M"
    using valid_TM_not_uniq.axioms[OF that]
    by (unfold_locales, unfold *)

  show ?thesis
  proof (rule iffI)
    from h1 h2 show "valid_TM_not_uniq M \<Longrightarrow> valid_TM ?M'" by (intro_locales) blast+

    assume "valid_TM ?M'"
    then have "valid_TM_not_uniq ?M'" by (fact valid_TM.axioms)
    note valid_TM_not_uniq.axioms[OF this, simplified]
    then show "valid_TM_not_uniq M" by (unfold_locales) (unfold next_fun_wrapper_simps)
  qed
qed

lemma valid_TM_I[intro]:
  fixes k \<Sigma> Q q\<^sub>0 F F\<^sub>A \<delta>\<^sub>q \<delta>\<^sub>w \<delta>\<^sub>m
  defines "(M :: ('q, 's) TM_record) \<equiv>  \<lparr> TM_record.tape_count = k, symbols = \<Sigma>,
    states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sub>A,
    next_state = \<delta>\<^sub>q, next_write = \<delta>\<^sub>w, next_move = \<delta>\<^sub>m \<rparr>"
  defines [simp]: "\<Sigma>\<^sub>t\<^sub>p \<equiv> options \<Sigma>"
  assumes at_least_one_tape: "k > 0"
    and symbol_axioms: "finite \<Sigma>" "\<Sigma> \<noteq> {}"
    and state_axioms: "finite Q" "q\<^sub>0 \<in> Q" "F \<subseteq> Q" "F\<^sub>A \<subseteq> F"
    and next_state_valid: "\<And>q hds. q \<in> Q \<Longrightarrow> length hds = k \<Longrightarrow> set hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p \<Longrightarrow> \<delta>\<^sub>q q hds \<in> Q"
    and next_write_valid: "\<And>q hds i. q \<in> Q \<Longrightarrow> length hds = k \<Longrightarrow> set hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p \<Longrightarrow> i < k \<Longrightarrow> \<delta>\<^sub>w q hds i \<in> \<Sigma>\<^sub>t\<^sub>p"
  shows "valid_TM (TM_default_wrapper M)"
  unfolding valid_TM_wrapper
proof (unfold_locales, unfold M_def TM_record.simps wf_hds_rec_simps)
  fix q hds
  assume "q \<in> Q" and wf: "length hds = k \<and> set hds \<subseteq> options \<Sigma>"
  with next_state_valid show "\<delta>\<^sub>q q hds \<in> Q" unfolding \<Sigma>\<^sub>t\<^sub>p_def by blast
  fix i
  assume "i < k"
  with next_write_valid and \<open>q \<in> Q\<close> and wf show "\<delta>\<^sub>w q hds i \<in> options \<Sigma>" unfolding \<Sigma>\<^sub>t\<^sub>p_def by blast
qed (fact assms)+

lemma valid_TM_finiteI:
  fixes M :: "('q, 's::finite) TM_record"
  assumes at_least_one_tape: "tape_count M > 0"
    and symbols_UNIV: "symbols M = UNIV"
    and state_axioms: "finite (states M)" "initial_state M \<in> states M"
    "final_states M \<subseteq> states M" "accepting_states M \<subseteq> final_states M"
    and next_state_valid: "\<And>q hds. q \<in> states M \<Longrightarrow> next_state M q hds \<in> states M"
  shows "valid_TM (TM_default_wrapper M)"
  unfolding valid_TM_wrapper
proof
  show "finite (symbols M)" by (fact finite_class.finite)
  show "symbols M \<noteq> {}" unfolding symbols_UNIV by (fact UNIV_not_empty)

  fix q hds i
  assume q: "q \<in> states M"
  then show "next_state M q hds \<in> states M" by (fact next_state_valid)
  show "next_write M q hds i \<in> tape_symbols_rec M" unfolding symbols_UNIV by simp
qed (fact assms)+

lemma valid_TM_finiteI'[intro]:
  fixes k Q q\<^sub>0 F F\<^sub>A \<delta>\<^sub>q \<delta>\<^sub>w \<delta>\<^sub>m
  defines "(M :: ('q, 's::finite) TM_record) \<equiv> \<lparr> TM_record.tape_count = k, symbols = UNIV,
    states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sub>A,
    next_state = \<delta>\<^sub>q, next_write = \<delta>\<^sub>w, next_move = \<delta>\<^sub>m \<rparr>"
  assumes at_least_one_tape: "k > 0"
    and state_axioms: "finite Q" "q\<^sub>0 \<in> Q" "F \<subseteq> Q" "F\<^sub>A \<subseteq> F"
    and next_state_valid: "\<And>q hds. q \<in> Q \<Longrightarrow> \<delta>\<^sub>q q hds \<in> Q"
  shows "valid_TM (TM_default_wrapper M)"
proof (intro valid_TM_finiteI, unfold M_def TM_record.simps)
  show "UNIV = UNIV" ..
qed (fact assms)+


text\<open>To define a type, we must prove that it is inhabited (there exist elements that have this type).
  For this we define the trivial ``rejecting TM'', and prove it to be valid.\<close>

definition rejecting_TM_rec :: "'q \<Rightarrow> 's \<Rightarrow> ('q, 's) TM_record"
  where "rejecting_TM_rec q0 s \<equiv> TM_default_wrapper \<lparr>
  tape_count = 1, symbols = {s},
  states = {q0}, initial_state = q0, final_states = {q0}, accepting_states = {},
  next_state = (\<lambda>q hds. q0), next_write = (\<lambda>q hds i. blank_symbol), next_move = (\<lambda>q hds i. No_Shift)
\<rparr>"

lemma rejecting_TM_valid: "valid_TM (rejecting_TM_rec q0 s)"
  unfolding rejecting_TM_rec_def by blast

text\<open>The type \<open>TM\<close> is then defined as the set of valid \<open>TM_record\<close>s.\<close>
(* TODO elaborate on the implications of this *)

typedef ('q, 's) TM = "{M :: ('q, 's) TM_record. valid_TM M}"
  using rejecting_TM_valid by fast

definition "rejecting_TM q0 s \<equiv> Abs_TM (rejecting_TM_rec q0 s)" (* TODO move this somewhere else *)

locale TM = TM_abbrevs +
  fixes M :: "('q, 's) TM"
begin

abbreviation "M_rec \<equiv> Rep_TM M"

text\<open>Note: The following definitions ``overwrite'' the \<open>TM_record\<close> field names (such as \<^const>\<open>TM_record.states\<close>).
  This is not detrimental as in \<^locale>\<open>TM\<close> contexts these shortcuts are more convenient.
  One mildly annoying consequence is, however, that when defining a TM using the record constructor
  inside \<^locale>\<open>TM\<close> contexts, \<^const>\<open>TM_record.tape_count\<close> must be specified explicitly with its full name. (see below for an example)
  Interestingly, this only applies to the first field (\<^const>\<open>TM_record.tape_count\<close>) and not any of the other ones.\<close>

definition tape_count where "tape_count \<equiv> TM_record.tape_count M_rec"
definition symbols where "symbols \<equiv> TM_record.symbols M_rec"
definition states where "states \<equiv> TM_record.states M_rec"
definition initial_state where "initial_state \<equiv> TM_record.initial_state M_rec"
definition final_states where "final_states \<equiv> TM_record.final_states M_rec"
definition accepting_states ("F\<^sup>+") where "F\<^sup>+ \<equiv> TM_record.accepting_states M_rec"
definition rejecting_states ("F\<^sup>-") where "F\<^sup>- \<equiv> final_states - accepting_states"
definition next_state where "next_state \<equiv> TM_record.next_state M_rec"
definition next_write where "next_write \<equiv> TM_record.next_write M_rec"
definition next_move  where "next_move  \<equiv> TM_record.next_move  M_rec"

lemmas TM_fields_defs = tape_count_def symbols_def
  states_def initial_state_def final_states_def accepting_states_def
  next_state_def next_write_def next_move_def

declare rejecting_states_def[simp]

text\<open>The following abbreviations are intentionally not implemented as \<^emph>\<open>notation\<close>,
  as notation is not transferred when interpreting locales (see section \<^emph>\<open>Usage\<close>).\<close>

abbreviation "k \<equiv> tape_count"
abbreviation "\<Sigma> \<equiv> symbols"
abbreviation "Q \<equiv> states"
abbreviation "q\<^sub>0 \<equiv> initial_state"
abbreviation "F \<equiv> final_states"
abbreviation "F\<^sub>A \<equiv> accepting_states"
abbreviation "F\<^sub>R \<equiv> rejecting_states"
abbreviation "\<delta>\<^sub>q \<equiv> next_state"
abbreviation "\<delta>\<^sub>w \<equiv> next_write"
abbreviation "\<delta>\<^sub>m \<equiv> next_move"

lemma M_rec[simp]: "M_rec = \<lparr> TM_record.tape_count = k, \<comment> \<open>as \<^const>\<open>TM.tape_count\<close> overwrites \<^const>\<open>TM_record.tape_count\<close>
        in \<^locale>\<open>TM\<close> contexts, it must be specified explicitly.\<close>
  symbols = \<Sigma>, states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sup>+,
  next_state = \<delta>\<^sub>q, next_write = \<delta>\<^sub>w, next_move  = \<delta>\<^sub>m \<rparr>"
  unfolding TM_fields_defs by simp


text\<open>\<^bold>\<open>Tape-symbols\<close> \<open>\<Sigma>\<^sub>t\<^sub>p\<close> is the set of valid symbols that may be written or read by \<^term>\<open>M\<close>.
  This includes all \<^emph>\<open>input symbols\<close> \<^const>\<open>\<Sigma>\<close> and the \<^const>\<open>blank_symbol\<close>.\<close>

abbreviation tape_symbols where "tape_symbols \<equiv> options symbols"
abbreviation "\<Sigma>\<^sub>t\<^sub>p \<equiv> tape_symbols"
lemma tape_symbols_altdef: "\<Sigma>\<^sub>t\<^sub>p = tape_symbols_rec M_rec" unfolding symbols_def ..
lemma tape_symbols_simps[iff]: "set_option s \<subseteq> \<Sigma> \<longleftrightarrow> s \<in> \<Sigma>\<^sub>t\<^sub>p" unfolding set_options_eq ..


text\<open>We provide the following shortcuts for ``unpacking'' the transition function.
  \<open>hds\<close> refers to the symbols currently under the TM heads.\<close>

(* this is currently unused, and only included for demonstration *)
definition transition :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> 'q \<times> ('s tp_symbol \<times> head_move) list"
  where "transition q hds = (\<delta>\<^sub>q q hds, map (\<lambda>i. (\<delta>\<^sub>w q hds i, \<delta>\<^sub>m q hds i)) [0..<k])"
abbreviation "\<delta> \<equiv> transition"

definition "next_writes q hds \<equiv> map (\<delta>\<^sub>w q hds) [0..<k]"
definition "next_moves q hds \<equiv> map (\<delta>\<^sub>m q hds) [0..<k]"
definition "next_actions q hds \<equiv> zip (next_writes q hds) (next_moves q hds)"
abbreviation "\<delta>\<^sub>a \<equiv> next_actions"

lemma next_actions_altdef: "\<delta>\<^sub>a q hds = map (\<lambda>i. (\<delta>\<^sub>w q hds i, \<delta>\<^sub>m q hds i)) [0..<k]"
  unfolding next_actions_def next_writes_def next_moves_def unfolding zip_map_map map2_same ..

lemma next_writes_simps[simp]:
  shows "i < k \<Longrightarrow> next_writes q hds ! i = \<delta>\<^sub>w q hds i"
    and "length (next_writes q hds) = k" unfolding next_writes_def by simp_all
lemma next_moves_simps[simp]:
  shows "i < k \<Longrightarrow> next_moves q hds ! i = \<delta>\<^sub>m q hds i"
    and "length (next_moves q hds) = k" unfolding next_moves_def by simp_all
lemma next_actions_simps[simp]:
  shows "i < k \<Longrightarrow> \<delta>\<^sub>a q hds ! i = (\<delta>\<^sub>w q hds i, \<delta>\<^sub>m q hds i)"
    and "length (next_actions q hds) = k" unfolding next_actions_def by simp_all


(* TODO document *)
abbreviation (input) "wf_hds hds \<equiv> length hds = k \<and> set hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p"

lemma wf_hds_M_rec[simp]: "wf_hds_rec M_rec = wf_hds"
  unfolding wf_hds_rec_def TM_fields_defs ..


subsubsection\<open>Properties\<close>

sublocale valid_TM M_rec using Rep_TM .. \<comment> \<open>The axioms of \<^locale>\<open>valid_TM\<close> hold by definition.\<close>

lemmas at_least_one_tape = at_least_one_tape[folded TM_fields_defs]
lemma at_least_one_tape': "k \<ge> 1" using at_least_one_tape unfolding One_nat_def by (fact Suc_leI)
lemmas symbol_axioms = symbol_axioms[folded TM_fields_defs]
lemmas state_axioms = state_axioms[folded TM_fields_defs]
lemma transition_axioms:
  assumes "q \<in> Q" and "length hds = k" and "set hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p"
  shows next_state_valid: "\<delta>\<^sub>q q hds \<in> Q"
    and next_write_valid: "i < k \<Longrightarrow> \<delta>\<^sub>w q hds i \<in> \<Sigma>\<^sub>t\<^sub>p"
  using assms unfolding TM_fields_defs by (blast intro: next_state_valid next_write_valid)+

lemmas TM_axioms = at_least_one_tape at_least_one_tape' state_axioms symbol_axioms transition_axioms
lemmas (in -) TM_axioms[simp, intro] = TM.TM_axioms

lemma final_states_valid[dest]: "q \<in> F \<Longrightarrow> q \<in> Q" using state_axioms(3) by blast
lemma accepting_states_final[dest]: "q \<in> F\<^sub>A \<Longrightarrow> q \<in> F" using state_axioms(4) by blast
lemma rejecting_states_final[dest]: "q \<in> F\<^sub>R \<Longrightarrow> q \<in> F" unfolding rejecting_states_def by blast

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


subsubsection\<open>Usage\<close>

text\<open>The following code showcases the usage of TM concepts in this draft:\<close>

notepad
begin
  fix M M\<^sub>1 :: "('q, 's) TM"

  interpret TM M .
  term \<delta>\<^sub>q
  term next_state
  thm state_axioms

  text\<open>Note that \<^emph>\<open>notation\<close> like \<open>F\<^sup>+\<close> is not available.\<close>

  interpret M\<^sub>1: TM M\<^sub>1 .
  term M\<^sub>1.\<delta>\<^sub>q
  term M\<^sub>1.next_state
  thm M\<^sub>1.state_axioms
end


subsubsection\<open>Symbols as Type\<close>

(* TODO document, motivate *)

locale typed_TM = TM M for M :: "('q, 's::finite) TM" +
  (* It is required to specify \<^typ>\<open>'s\<close> as \<^class>\<open>finite\<close> here,
     even though this could be inferred from the assumption below. See \<^url>\<open>https://stackoverflow.com/a/72136728/9335596\<close> *)
  assumes symbols_UNIV[simp, intro]: "TM.symbols M = UNIV"
begin

text\<open>The added assumption that all members of \<^typ>\<open>'s\<close> are valid symbols
  allows for simpler axioms.\<close>

lemma tape_symbols_UNIV[simp]: "\<Sigma>\<^sub>t\<^sub>p = UNIV" using symbols_UNIV unfolding symbols_def by blast

lemma next_state_valid[intro]: "q \<in> Q \<Longrightarrow> length hds = k \<Longrightarrow> \<delta>\<^sub>q q hds \<in> Q" by fastforce

lemmas symbol_simps = symbols_UNIV tape_symbols_UNIV
lemmas TM_axioms = at_least_one_tape state_axioms symbol_simps next_state_valid

end

lemma typed_TM_I:
  assumes "valid_TM M_rec"
    and "symbols M_rec = UNIV"
  shows "typed_TM (Abs_TM M_rec)"
proof (unfold_locales)
  have "TM.symbols (Abs_TM M_rec) = symbols (Rep_TM (Abs_TM M_rec))" unfolding TM.symbols_def ..
  also from \<open>valid_TM M_rec\<close> have "... = symbols M_rec" by (subst Abs_TM_inverse) blast+
  finally show "TM.symbols (Abs_TM M_rec) = UNIV" unfolding \<open>symbols M_rec = UNIV\<close> .
qed


subsection\<open>Turing Machine State\<close>

subsubsection\<open>Tapes\<close>

text\<open>We describe a TM tape following @{cite forsterCoqTM2020} as a datatype containing:\<close>

datatype 's tape = Tape
  (left: "'s tp_symbol list") \<comment> \<open>the lists of symbols currently left of the TM head\<close>
  (head: "'s tp_symbol") \<comment> \<open>the symbol currently under the TM head\<close>
  (right: "'s tp_symbol list") \<comment> \<open>the lists of symbols currently right of the TM head\<close>

text\<open>For both \<^const>\<open>left\<close> and \<^const>\<open>right\<close>, the \<open>n\<close>-th element represents the symbol reached
  by \<open>n\<close> consecutive moves left (\<^const>\<open>Shift_Left\<close>) or right (\<^const>\<open>Shift_Right\<close>) resp.
  The tape is assumed to be infinite in both directions (containing \<^const>\<open>blank_symbol\<close>s),
  so blanks will be inserted into the record if the TM crosses the ``ends''.

  We chose this approach as compared to letting the symbol under the head
  be the first element of \<open>right\<close>@{cite xuIsabelleTM2013}, as it allows symmetry for move-actions.
  Our definition of tapes allows no completely empty tape (with size zero; containing zero symbols),
  as the \<^const>\<open>head\<close> symbol is always set, such that even the empty tape has size \<open>1\<close>.
  However, this makes sense concerning space-complexity,
  as a TM (depending on the exact definition) always reads at least one cell
  (and thus matches the requirement for space-complexity-functions to be at least \<open>1\<close>
  from @{cite hopcroftAutomata1979}).

  The use of datatype (as compared to record, for instance) grants the predefined
  \<^const>\<open>map_tape\<close> and \<^const>\<open>set_tape\<close>, including useful lemmas.\<close>

abbreviation empty_tape where "empty_tape \<equiv> Tape [] blank_symbol []"

lemma tape_map_ident0[simp]: "map_tape (\<lambda>x. x) = (\<lambda>x. x)" by (rule ext) (rule tape.map_ident)


context TM_abbrevs
begin

text\<open>The following notation definitions would seem to be a good use case for \<open>syntax\<close> and \<open>translation\<close>
  (see for instance \<^term>\<open>\<exists>\<^sub>\<le>\<^sub>1x. P x\<close>, the syntax for \<^const>\<open>Uniq\<close>).
  Unfortunately, defining translations within a locale is not possible.
  The upside of this approach however, is that it allows inspection via \<^emph>\<open>Ctrl+Mouseover\<close> and \<^emph>\<open>Ctrl+Click\<close>,
  making it more accessible to users unfamiliar with the notation.\<close>

notation Tape ("\<langle>_|_|_\<rangle>")
abbreviation Tape_no_left ("\<langle>|_|_\<rangle>") where "\<langle>|h|r\<rangle> \<equiv> \<langle>[]|h|r\<rangle>"
abbreviation Tape_no_right ("\<langle>_|_|\<rangle>") where "\<langle>l|h|\<rangle> \<equiv> \<langle>l|h|[]\<rangle>"
abbreviation Tape_no_left_no_right ("\<langle>|_|\<rangle>") where "\<langle>|h|\<rangle> \<equiv> \<langle>[]|h|[]\<rangle>"
notation empty_tape ("\<langle>\<rangle>")

text\<open>The following lemmas should be useful in cases
  when expanding a tape \<open>tp\<close> into \<open>\<langle>l|h|r\<rangle>\<close> is inconvenient.\<close>

corollary set_tape_simps[simp]: "set_tape \<langle>l|h|r\<rangle> = \<Union> (set_option ` (set l \<union> {h} \<union> set r))"
  unfolding tape.set by blast
corollary set_tape_def: "set_tape tp = \<Union> (set_option ` (set (left tp) \<union> {head tp} \<union> set (right tp)))"
  by (induction tp) (unfold set_tape_simps tape.sel, rule refl)

lemma set_tape_finite: "finite (set_tape tp)"
proof (induction tp)
  case (Tape l h r)
  have "finite (\<Union> (set_option ` set xs))" for xs :: "'a option list" by (intro finite_UN_I) auto
  moreover have "finite (set_option x)" for x :: "'a option" by (rule finite_set_option)
  ultimately show ?case unfolding tape.set by (intro finite_UnI)
qed

lemma (in TM) set_tape_valid[dest]: "set_tape tp \<subseteq> \<Sigma> \<Longrightarrow> head tp \<in> \<Sigma>\<^sub>t\<^sub>p"
proof (induction tp)
  case (Tape l h r)
  assume "set_tape \<langle>l|h|r\<rangle> \<subseteq> \<Sigma>"
  then have "set_option h \<subseteq> \<Sigma>" by simp
  then show "head \<langle>l|h|r\<rangle> \<in> \<Sigma>\<^sub>t\<^sub>p" unfolding tape.sel by (induction h) blast+
qed

corollary map_tape_def[unfolded Let_def]:
  "map_tape f tp = (let f' = map_option f in \<langle>map f' (left tp)|f' (head tp)|map f' (right tp)\<rangle>)"
  unfolding Let_def by (induction tp) simp

text\<open>We define the size of a tape as the number of cells the TM has visited.
  Even though the tape is considered infinite, this can be used for exploring space requirements.
  Note that \<^const>\<open>size\<close> \<^footnote>\<open>defined by the datatype command, see for instance @{thm tape.size(2)}\<close>
  is not of use in this case, since it applies \<^const>\<open>size\<close> recursively,
  such that the \<^const>\<open>size\<close> of the tape depends on the \<^const>\<open>size\<close> of the tape symbols and not just their number.\<close>

definition tape_size :: "'s tape \<Rightarrow> nat"
  where "tape_size tp \<equiv> length (left tp) + length (right tp) + 1"

lemma tape_size_simps[simp]: "tape_size \<langle>l|h|r\<rangle> = length l + length r + 1"
  unfolding tape_size_def by simp

lemma map_tape_size[simp]: "tape_size (map_tape f tp) = tape_size tp"
  unfolding tape_size_def tape.map_sel by simp

lemma set_tape_size[simp]: "card (set_tape tp) \<le> tape_size tp"
proof (induction tp)
  case (Tape l h r)
  let ?S = "set l \<union> {h} \<union> set r"

  have "card (set_tape \<langle>l|h|r\<rangle>) = card (\<Union> (set_option ` ?S))" unfolding set_tape_simps ..
  also have "... \<le> (\<Sum>s\<in>?S. card (set_option s))" by (rule card_UN_le) blast
  also have "... \<le> (\<Sum>s\<in>?S. 1)" using card_set_option by (rule sum_mono)
  also have "... = card ?S" using card_eq_sum ..
  also have "... \<le> card (set l \<union> {h}) + card (set r)" by (fact card_Un_le)
  also have "... \<le> card (set l) + card {h} + card (set r)"
    unfolding add_le_cancel_right by (fact card_Un_le)
  also have "... \<le> tape_size \<langle>l|h|r\<rangle>" unfolding tape_size_simps by (simp add: add_mono card_length)
  finally show "card (set_tape \<langle>l|h|r\<rangle>) \<le> tape_size \<langle>l|h|r\<rangle>" .
qed

lemma empty_tape_size[simp]: "tape_size \<langle>\<rangle> = 1" by simp

end \<comment> \<open>\<^locale>\<open>TM_abbrevs\<close>\<close>


subsubsection\<open>Configuration\<close>

text\<open>We define a TM \<^emph>\<open>configuration\<close> as a datatype of:\<close>

datatype ('q, 's) TM_config = TM_config
  (state: 'q) \<comment> \<open>the current state\<close>
  (tapes: "'s tape list") \<comment> \<open>current contents of all tapes\<close>

text\<open>Combined with the \<^typ>\<open>('q, 's) TM\<close> definition,
  it completely describes a TM at any time during its execution.\<close>

(* helpful lemmas complementing the ones generated by datatype *)
declare TM_config.map_sel[simp]
lemmas TM_config_eq = TM_config.expand[OF conjI] (* sadly, \<open>datatype\<close> does not provide this directly (cf. \<open>some_record.equality\<close> defined by \<open>record\<close> *)

abbreviation (in TM_abbrevs) "map_conf_state f \<equiv> map_TM_config f (\<lambda>s. s)"
abbreviation (in TM_abbrevs) "map_conf_tapes f \<equiv> map_TM_config (\<lambda>q. q) f"


paragraph\<open>Symbols currently under the TM-heads\<close>

abbreviation heads :: "('q, 's) TM_config \<Rightarrow> 's tp_symbol list"
  where "heads c \<equiv> map head (tapes c)"

lemma map_head_tapes[simp]:
  shows "map head (map (map_tape f) tps) = map (map_option f) (map head tps)"
    and "map (head \<circ> map_tape f) tps = map (map_option f) (map head tps)"
  by (simp_all only: map_map comp_def tape.map_sel)


context TM
begin

paragraph\<open>Final configurations\<close>

abbreviation (in TM) is_final :: "('q, 's) TM_config \<Rightarrow> bool" where
  "is_final c \<equiv> state c \<in> F"

lemma (in TM) is_final_altdef: "is_final c \<longleftrightarrow> state c \<in> F\<^sup>+ \<or> state c \<in> F\<^sup>-"
  using state_axioms(4) unfolding rejecting_states_def by blast


paragraph\<open>Well-formed configurations\<close>

text\<open>A \<^typ>\<open>('q, 's) TM_config\<close> \<open>c\<close> is considered well-formed w.r.t. a TM \<open>M\<close>,
  iff the number of \<^const>\<open>tapes\<close> of \<open>c\<close> matches the number of tapes of \<open>M\<close>.\<close>

definition wf_config :: "('q, 's) TM_config \<Rightarrow> bool"
  where "wf_config c \<equiv> state c \<in> Q \<and> length (tapes c) = k
    \<and> (\<forall>tp\<in>set (tapes c). set_tape tp \<subseteq> \<Sigma>)"

mk_ide wf_config_def |intro wf_configI[intro]|

lemma tapes_heads_valid:
  assumes "\<forall>tp\<in>set (tapes c). set_tape tp \<subseteq> \<Sigma>"
  shows "set (heads c) \<subseteq> \<Sigma>\<^sub>t\<^sub>p"
  using assms unfolding Ball_set_map by blast

lemma wf_config_hds:
  assumes "wf_config c"
  shows "length (heads c) = k"
    and "set (heads c) \<subseteq> \<Sigma>\<^sub>t\<^sub>p"
  using assms unfolding wf_config_def by (simp, blast intro!: tapes_heads_valid)

lemma wf_config_iff: "wf_config c \<longleftrightarrow> state c \<in> Q \<and> length (tapes c) = k
    \<and> (\<forall>tp\<in>set (tapes c). set_tape tp \<subseteq> \<Sigma>) \<and> wf_hds (heads c)"
  by (intro iffI conjI wf_configI) (use wf_config_def[iff] in \<open>blast intro!: wf_config_hds\<close>)+

mk_ide wf_config_iff |dest wf_configD[dest]| |elim wf_configE[elim]|

lemma (in typed_TM) wf_config_def: "wf_config c \<longleftrightarrow> state c \<in> Q \<and> length (tapes c) = k"
  unfolding wf_config_def by simp

lemma
  assumes "wf_config c"
  shows wf_config_tapes_nonempty'[dest]: "0 < length (tapes c)"
    and wf_config_tapes_nonempty[dest?]: "tapes c \<noteq> []"
proof -
  from \<open>wf_config c\<close> have "length (tapes c) = k" ..
  then show "0 < length (tapes c)" by simp
  then show "tapes c \<noteq> []" by simp
qed

lemma wf_config_last[dest, intro]: "wf_config c \<Longrightarrow> set_tape (last (tapes c)) \<subseteq> \<Sigma>" by auto

lemma next_fun_wrapper_simps:
  fixes f val c
  defines "q \<equiv> state c"
    and "hds \<equiv> heads c"
    and "f' \<equiv> next_fun_wrapper val k \<Sigma> Q f"
  assumes "wf_config c"
  shows "i < k \<Longrightarrow> f' q hds i = f q hds i"
    and "f' q hds 0 = f q hds 0"
proof -
  from \<open>wf_config c\<close> show "i < k \<Longrightarrow> f' q hds i = f q hds i" for i
    unfolding assms by (subst next_fun_wrapper_simps) blast+
  then show "f' q hds 0 = f q hds 0" by blast
qed


end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


subsection\<open>TM Execution\<close>

subsubsection\<open>Actions\<close>

context TM_abbrevs
begin

paragraph\<open>TM Head Movement\<close>

text\<open>To execute a TM tape \<^typ>\<open>head_move\<close>, we shift the entire tape by one element.
  If the tape head is at the ``end'' of the defined tape, we insert \<^const>\<open>blank_symbol\<close>s,
  as the tape is considered infinite in both directions.\<close>

(* TODO split into shiftL and shiftR (maybe use symmetry) *)
fun tape_shift :: "head_move \<Rightarrow> 's tape \<Rightarrow> 's tape" where
  "tape_shift Shift_Left  \<langle>|h|rs\<rangle>     = \<langle>|Bk|h#rs\<rangle>"
| "tape_shift Shift_Left  \<langle>l#ls|h|rs\<rangle> = \<langle>ls|l |h#rs\<rangle>"
| "tape_shift Shift_Right \<langle>ls|h|\<rangle>     = \<langle>h#ls|Bk|\<rangle>"
| "tape_shift Shift_Right \<langle>ls|h|r#rs\<rangle> = \<langle>h#ls|r |rs\<rangle>"
| "tape_shift No_Shift    tp = tp"

lemma tape_shift_set[simp]: "set_tape (tape_shift m tp) = set_tape tp"
proof (induction tp)
  case (Tape l h r)
  show ?case
  proof (induction m)
    case Shift_Left show ?case by (induction l) auto next
    case Shift_Right show ?case by (induction r) auto
  qed simp
qed

lemma tape_shift_map[simp]: "map_tape f (tape_shift m tp) = tape_shift m (map_tape f tp)"
proof (induction tp)
  case (Tape l h r)
  show ?case
  proof (induction m)
    case Shift_Left  show ?case by (induction l) auto next
    case Shift_Right show ?case by (induction r) auto
  qed simp
qed


paragraph\<open>Write Symbols\<close>

text\<open>Write a symbol to the current position of the TM tape head.\<close>

definition tape_write :: "'s tp_symbol \<Rightarrow> 's tape \<Rightarrow> 's tape"
  where "tape_write s tp = \<langle>left tp|s|right tp\<rangle>"

corollary tape_write_simps[simp]: "tape_write s \<langle>l|h|r\<rangle> = \<langle>l|s|r\<rangle>" unfolding tape_write_def by simp
corollary tape_write_id[simp]: "tape_write (head tp) tp = tp" by (induction tp) simp

lemma tape_write_map[simp]:
  "tape_write (map_option f s) (map_tape f tp) = map_tape f (tape_write s tp)"
  by (induction tp) simp

lemma tape_write_set: "set_tape (tape_write s tp) \<subseteq> set_option s \<union> set_tape tp"
  by (induction tp) auto


paragraph\<open>Tape Action\<close>

text\<open>Write a symbol, then move the head.\<close>

definition tape_action :: "('s tp_symbol \<times> head_move) \<Rightarrow> 's tape \<Rightarrow> 's tape"
  where "tape_action a tp = tape_shift (snd a) (tape_write (fst a) tp)"

corollary tape_action_altdef: "tape_action (s, m) = tape_shift m \<circ> tape_write s"
  unfolding tape_action_def by auto

lemma tape_action_id[simp]: "tape_action (head tp, No_Shift) tp = tp"
  unfolding tape_action_altdef by simp

lemma tape_action_map[simp]:
  "tape_action (map_option f s, m) (map_tape f tp) = map_tape f (tape_action (s, m) tp)"
  unfolding tape_action_def by simp

lemma tape_action_set: "set_tape (tape_action (s, m) tp) \<subseteq> set_option s \<union> set_tape tp"
  unfolding tape_action_def tape_shift_set fst_conv by (fact tape_write_set)

end \<comment> \<open>\<^locale>\<open>TM_abbrevs\<close>\<close>


subsubsection\<open>Steps\<close>

context TM
begin

definition step_not_final :: "('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config"
  where "step_not_final c = (let q=state c; hds=heads c in TM_config
      (next_state q hds)
      (map2 tape_action (next_actions q hds) (tapes c)))"

lemma step_not_final_simps[simp]:
  shows "state (step_not_final c) = \<delta>\<^sub>q (state c) (heads c)"
    and "tapes (step_not_final c) = map2 tape_action (\<delta>\<^sub>a (state c) (heads c)) (tapes c)"
  unfolding step_not_final_def by (simp_all add: Let_def)

lemma step_not_final_eqI:
  assumes l: "length tps = k"
    and l': "length tps' = k"
    and "\<And>i. i < k \<Longrightarrow> tape_action (\<delta>\<^sub>w q hds i, \<delta>\<^sub>m q hds i) (tps ! i) = tps' ! i"
  shows "map2 tape_action (next_actions q hds) tps = tps'"
proof (rule nth_equalityI, unfold length_map length_zip next_actions_simps l l' min.idem)
  fix i assume "i < k"
  then have [simp]: "[0..<k] ! i = i" by simp

  from \<open>i < k\<close> have "map2 tape_action (\<delta>\<^sub>a q hds) tps ! i = tape_action (\<delta>\<^sub>a q hds ! i) (tps ! i)"
    by (intro nth_map2) (auto simp add: l)
  also from \<open>i < k\<close> have "... = tape_action (\<delta>\<^sub>w q hds i, \<delta>\<^sub>m q hds i) (tps ! i)" by simp
  also from assms(3) and \<open>i < k\<close> have "... = tps' ! i" .
  finally show "map2 tape_action (\<delta>\<^sub>a q hds) tps ! i = tps' ! i" .
qed (rule refl)

text\<open>If the current state is not final,
  apply the action determined by \<^const>\<open>\<delta>\<close> for the current configuration.
  Otherwise, do not execute any action.\<close>
definition step :: "('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config"
  where "step c = (if state c \<in> F then c else step_not_final c)"

abbreviation "steps n \<equiv> step ^^ n"

corollary step_simps[intro, simp]:
  shows step_final: "is_final c \<Longrightarrow> step c = c"
    and step_not_final: "\<not> is_final c \<Longrightarrow> step c = step_not_final c"
  unfolding step_def by auto

corollary steps_plus[simp]: "steps n2 (steps n1 c) = steps (n1 + n2) c"
  unfolding add.commute[of n1 n2] funpow_add comp_def ..

paragraph\<open>Final Steps\<close>

lemma final_steps[simp, intro]: "is_final c \<Longrightarrow> steps n c = c"
  by (rule funpow_fixpoint) (rule step_final)

corollary final_step_final[intro]: "is_final c \<Longrightarrow> is_final (step c)" by simp
corollary final_steps_final[intro]: "is_final c \<Longrightarrow> is_final (steps n c)" by simp

lemma final_le_steps[dest]:
  assumes "is_final (steps n c)" and "n \<le> m"
  shows "steps m c = steps n c"
proof -
  from \<open>n \<le> m\<close> obtain x where "m = x + n" unfolding le_iff_add by force
  have "(step^^m) c = (step^^x) ((step^^n) c)" unfolding \<open>m = x + n\<close> funpow_add by simp
  also have "... = (step^^n) c" using \<open>is_final (steps n c)\<close> by blast
  finally show "steps m c = steps n c" .
qed

corollary final_mono[dest]:
  assumes "is_final (steps n c)"
    and "n \<le> m"
  shows "is_final (steps m c)"
  unfolding final_le_steps[OF assms] by (fact \<open>is_final (steps n c)\<close>)

corollary final_mono': "mono (\<lambda>n. is_final (steps n c))"
  using final_mono by (intro monoI le_boolI)

lemma final_steps_rev[intro]:
  assumes "is_final (steps n c)"
    and "is_final (steps m c)"
  shows "steps n c = steps m c"
proof (cases n m rule: le_cases)
  case le with assms show ?thesis by (intro final_le_steps[symmetric]) next
  case ge with assms show ?thesis by (intro final_le_steps)
qed

lemma final_steps_le[dest]:
  assumes "\<not> is_final (steps n1 c)"
    and "is_final (steps n2 c)"
  shows "n1 < n2"
  using assms and TM.final_mono linorder_le_less_linear by blast

lemma final_steps_ex_eq[simp]: "(\<exists>n\<le>N. is_final (steps n c)) \<longleftrightarrow> is_final (steps N c)" by blast


paragraph\<open>Well-Formed Steps\<close>

lemma step_nf_l_tps: "length (tapes c) = k \<Longrightarrow> length (tapes (step_not_final c)) = k" by simp
lemma wf_step_not_final[intro]: "wf_config c \<Longrightarrow> wf_config (step_not_final c)"
proof (elim wf_configE, intro wf_configI)
  let ?q = "state c" and ?tps = "tapes c" and ?hds = "heads c"
    and ?tps' = "tapes (step_not_final c)"

  assume q: "?q \<in> Q" and l[simp]: "length ?tps = k" and wf: "length ?hds = k" "set ?hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p"
  from l have l': "length ?tps' = k" by (fact step_nf_l_tps)

  assume valid_tps: "\<forall>tp\<in>set ?tps. set_tape tp \<subseteq> \<Sigma>"
  then show "\<forall>tp\<in>set ?tps'. set_tape tp \<subseteq> \<Sigma>" unfolding all_set_conv_all_nth l l'
  proof (elim cond_All_mono)
    fix i assume [simp]: "i < k"
    have "set_tape (?tps' ! i) = set_tape (tape_action (\<delta>\<^sub>a ?q ?hds ! i) (?tps ! i))"
      unfolding step_not_final_simps by (subst nth_map2) simp_all
    also have "... \<subseteq> set_option (\<delta>\<^sub>w ?q ?hds i) \<union> set_tape (?tps ! i)" by (simp add: tape_action_set)
    also have "... \<subseteq> \<Sigma>"
    proof (rule Un_least)
      from q and valid_tps and wf and \<open>i < k\<close> show "set_option (\<delta>\<^sub>w ?q ?hds i) \<subseteq> \<Sigma>" by blast
      from valid_tps show "set_tape (?tps ! i) \<subseteq> \<Sigma>" by simp
    qed
    finally show "set_tape (?tps' ! i) \<subseteq> \<Sigma>" .
  qed
qed auto

lemma step_l_tps: "length (tapes c) = k \<Longrightarrow> length (tapes (step c)) = k" by (cases "is_final c") auto
lemma wf_step[intro]: "wf_config c \<Longrightarrow> wf_config (step c)" by (cases "is_final c") auto

lemma steps_l_tps: "length (tapes c) = k \<Longrightarrow> length (tapes (steps n c)) = k" using step_l_tps by (elim funpow_induct)
lemma wf_steps[intro]: "wf_config c \<Longrightarrow> wf_config (steps n c)" using wf_step by (elim funpow_induct)

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>

end
