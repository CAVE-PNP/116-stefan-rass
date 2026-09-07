section\<open>A Theory of Turing Machines\<close>

theory TM
  imports Main
    "Supplementary/Lists" "Supplementary/Option_S"
    "Intro_Dest_Elim.IHOL_IDE" "HOL-Library.Countable"
begin


subsection\<open>Prerequisites\<close>

text\<open>We introduce the locale \<open>TM_abbrevs\<close> to scope local abbreviations.
  This allows easy access to notation without introducing possible bloat on the global scope.
  In other words, users of this theory have to \<^emph>\<open>opt-in\<close> to more specialized abbreviations.
  The idea for this is from the Style Guide for Contributors to IsarMathLib\<^footnote>\<open>\<^url>\<open>https://www.nongnu.org/isarmathlib/IsarMathLib/CONTRIBUTING.html\<close>\<close>.\<close>
locale TM_abbrevs

(* TODO consider extracting these to some other theory *)
type_synonym ('symbol) word = "'symbol list" (* TODO it seems "word" is not actually used anywhere. use or remove. *)

datatype head_move = Shift_Left | Shift_Right | No_Shift


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

(* consider introducing a type of actions:
 * type_synonym (in TM_abbrevs) ('s) action = "'s tp_symbol \<times> head_move" *)

subsection\<open>Turing Machines\<close>

text\<open>We model a (\<^typ>\<open>'l\<close>-labelled @{cite forsterCoqTM2020}, deterministic, \<open>k\<close>-tape) TM over the type \<^typ>\<open>'q\<close> of states
  and the finite type \<^typ>\<open>'s\<close> of symbols, as a tuple of:\<close>

record ('q, 's, 'l) TM_record =
  tape_count :: nat \<comment> \<open>\<open>k\<close>, the number of tapes\<close>
  symbols :: "'s set" \<comment> \<open>\<open>\<Sigma>\<close>, the set of symbols, not including the \<^const>\<open>blank_symbol\<close>\<close>
  states :: "'q set" \<comment> \<open>\<open>Q\<close>, the set of states\<close>
  initial_state :: 'q \<comment> \<open>\<open>q\<^sub>0 \<in> Q\<close>, the initial state; computation will start on \<open>k\<close> blank tapes in this state\<close>
  final_states :: "'q set" \<comment> \<open>\<open>F \<subseteq> Q\<close>, the set of final states; if a TM is in a final state,
    its computation is considered finished (the TM has halted) and no further steps will be executed\<close>
  label :: "'q \<Rightarrow> 'l" \<comment> \<open>\<open>lab\<close>, the labelling function used to distinguish final states (see @{cite forsterCoqTM2020})\<close>

  next_state :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> 'q" \<comment> \<open>Maps the current state and vector of read symbols to the next state.\<close>
  next_write :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> nat \<Rightarrow> 's tp_symbol" \<comment> \<open>Maps the current state, read symbols and tape index
    to the symbol to write before transitioning to the next state.\<close>
  next_move  :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> nat \<Rightarrow> head_move" \<comment> \<open>Maps the current state, read symbols and tape index
    to the head movement to perform before transitioning to the next state.\<close>

abbreviation "TM k \<Sigma> Q q\<^sub>0 F lab \<delta>\<^sub>q \<delta>\<^sub>w \<delta>\<^sub>m \<equiv> \<lparr> TM_record.tape_count = k, symbols = \<Sigma>,
    states = Q, initial_state = q\<^sub>0, final_states = F, label = lab,
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
abbreviation tape_symbols_rec :: "('q, 's, 'l) TM_record \<Rightarrow> 's tp_symbol set"
  where "tape_symbols_rec M_rec \<equiv> options (symbols M_rec)"


paragraph\<open>Well-formed\<close>

text\<open>A vector \<open>hds\<close> of symbols currently under the TM-heads,
  is considered a well-formed state w.r.t. a TM \<open>M\<close>,
  iff the number of elements of \<open>hds\<close> matches the number of tapes of \<open>M\<close>,
  and all elements are valid symbols for \<open>M\<close>.\<close>

definition wf_hds_rec :: "('q, 's, 'l) TM_record \<Rightarrow> 's tp_symbol list \<Rightarrow> bool"
  where "wf_hds_rec M_rec hds \<equiv> length hds = tape_count M_rec \<and> set hds \<subseteq> tape_symbols_rec M_rec"

lemma wf_hds_rec_simps[simp]: "wf_hds_rec \<lparr>
    TM_record.tape_count = k, symbols = \<Sigma>,
    states = Q, initial_state = q\<^sub>0, final_states = F, label = lab,
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

locale valid_TM =
  fixes M :: "('q, 's, 'l) TM_record"
  assumes at_least_one_tape: "tape_count M > 0" (* TODO motivate this assm. "why is this necessary?" edit: initial_config would have to be defined differently *)
    and symbol_axioms: "finite (symbols M)" "symbols M \<noteq> {}"
    and state_axioms: "finite (states M)" "initial_state M \<in> states M"
      "final_states M \<subseteq> states M"
    and next_state_valid: "\<And>q hds. q \<in> states M \<Longrightarrow> wf_hds_rec M hds \<Longrightarrow> next_state M q hds \<in> states M"
    and next_write_valid: "\<And>q hds i. q \<in> states M \<Longrightarrow> wf_hds_rec M hds \<Longrightarrow> i < tape_count M \<Longrightarrow>
          next_write M q hds i \<in> tape_symbols_rec M"
begin
lemmas axioms = at_least_one_tape symbol_axioms state_axioms next_state_valid next_write_valid
end

text\<open>Notes on assumptions.
  Many of these assumptions would be trivial to satisfy when explicitly constructing a TM,
  especially the premises of \<open>next_state_valid\<close> and \<open>next_write_valid\<close>.
  They are, however, very useful when constructing TMs from other TMs.\<close>

lemma valid_TM_I[intro]:
  fixes k \<Sigma> Q q\<^sub>0 F lab \<delta>\<^sub>q \<delta>\<^sub>w \<delta>\<^sub>m
  defines "(M :: ('q, 's, 'l) TM_record) \<equiv>  \<lparr> TM_record.tape_count = k, symbols = \<Sigma>,
    states = Q, initial_state = q\<^sub>0, final_states = F, label = lab,
    next_state = \<delta>\<^sub>q, next_write = \<delta>\<^sub>w, next_move = \<delta>\<^sub>m \<rparr>"
  defines [simp]: "\<Sigma>\<^sub>t\<^sub>p \<equiv> options \<Sigma>"
  assumes at_least_one_tape: "k > 0"
    and symbol_axioms: "finite \<Sigma>" "\<Sigma> \<noteq> {}"
    and state_axioms: "finite Q" "q\<^sub>0 \<in> Q" "F \<subseteq> Q"
    and next_state_valid: "\<And>q hds. q \<in> Q \<Longrightarrow> length hds = k \<Longrightarrow> set hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p \<Longrightarrow> \<delta>\<^sub>q q hds \<in> Q"
    and next_write_valid: "\<And>q hds i. q \<in> Q \<Longrightarrow> length hds = k \<Longrightarrow> set hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p \<Longrightarrow> i < k \<Longrightarrow> hds ! i \<in> \<Sigma>\<^sub>t\<^sub>p \<Longrightarrow> \<delta>\<^sub>w q hds i \<in> \<Sigma>\<^sub>t\<^sub>p"
  shows "valid_TM M"
proof (unfold_locales, unfold M_def TM_record.simps wf_hds_rec_simps)
  fix q hds
  assume "q \<in> Q" and wf: "length hds = k \<and> set hds \<subseteq> options \<Sigma>"
  with next_state_valid show "\<delta>\<^sub>q q hds \<in> Q" unfolding \<Sigma>\<^sub>t\<^sub>p_def by blast
  fix i
  assume "i < k"
  with wf have "hds ! i \<in> \<Sigma>\<^sub>t\<^sub>p" by force
  with next_write_valid and \<open>q \<in> Q\<close> and wf and \<open>i < k\<close> show "\<delta>\<^sub>w q hds i \<in> options \<Sigma>"
    unfolding \<Sigma>\<^sub>t\<^sub>p_def by blast
qed (fact assms)+

lemma valid_TM_finiteI[intro]:
  fixes k Q q\<^sub>0 F lab \<delta>\<^sub>q \<delta>\<^sub>w \<delta>\<^sub>m and M :: "('q, 's::finite, 'l) TM_record"
  defines "M \<equiv> TM k UNIV Q q\<^sub>0 F lab \<delta>\<^sub>q \<delta>\<^sub>w \<delta>\<^sub>m"
  assumes at_least_one_tape: "k > 0"
    and state_axioms: "finite Q" "q\<^sub>0 \<in> Q" "F \<subseteq> Q"
    and next_state_valid: "\<And>q hds. q \<in> Q \<Longrightarrow> \<delta>\<^sub>q q hds \<in> Q"
  shows "valid_TM M"
proof (unfold_locales, unfold M_def TM_record.simps)
  show "finite (UNIV::'s set)" by (fact finite_class.finite_UNIV)
  show "UNIV \<noteq> {}" by (fact UNIV_not_empty)

  fix q hds i
  show "\<delta>\<^sub>w q hds i \<in> options UNIV" by simp
  assume q: "q \<in> Q"
  then show "\<delta>\<^sub>q q hds \<in> Q" by (fact next_state_valid)
qed (fact assms)+


text\<open>To define a type, we must prove that it is inhabited (there exist elements that have this type).
  For this we define the trivial ``halting TM'', and prove it to be valid.\<close>

definition halting_TM_rec :: "'q \<Rightarrow> 's set \<Rightarrow> 'l \<Rightarrow> ('q, 's, 'l) TM_record"
  where "halting_TM_rec q0 \<Sigma> l \<equiv> \<lparr>
  tape_count = 1, symbols = \<Sigma>,
  states = {q0}, initial_state = q0, final_states = {q0}, label = (\<lambda>q. l),
  next_state = (\<lambda>q hds. q), next_write = (\<lambda>q hds i. hds ! i), next_move = (\<lambda>q hds i. No_Shift)
\<rparr>"

lemma halting_TM_valid: "finite \<Sigma> \<Longrightarrow> \<Sigma> \<noteq> {} \<Longrightarrow> valid_TM (halting_TM_rec q0 \<Sigma> l)"
  unfolding halting_TM_rec_def by (unfold_locales) (auto simp: subset_eq)

text\<open>The type \<open>TM\<close> is then defined as the set of valid \<open>TM_record\<close>s.\<close>
(* TODO elaborate on the implications of this *)

typedef ('q, 's, 'l) TM = "{M :: ('q, 's, 'l) TM_record. valid_TM M}"
  using halting_TM_valid by fast

locale TM = TM_abbrevs +
  fixes M :: "('q, 's, 'l) TM"
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
definition label where "label \<equiv> TM_record.label M_rec"
definition next_state where "next_state \<equiv> TM_record.next_state M_rec"
definition next_write where "next_write \<equiv> TM_record.next_write M_rec"
definition next_move  where "next_move  \<equiv> TM_record.next_move  M_rec"

lemmas TM_fields_defs = tape_count_def symbols_def
  states_def initial_state_def final_states_def label_def
  next_state_def next_write_def next_move_def


text\<open>The following abbreviations are intentionally not implemented as \<^emph>\<open>notation\<close>,
  as notation is not transferred when interpreting locales (see section \<^emph>\<open>Usage\<close>).\<close>

abbreviation "k \<equiv> tape_count"
abbreviation "\<Sigma> \<equiv> symbols"
abbreviation "Q \<equiv> states"
abbreviation "q\<^sub>0 \<equiv> initial_state"
abbreviation "F \<equiv> final_states"
abbreviation (input) "lab \<equiv> label"
abbreviation "\<delta>\<^sub>q \<equiv> next_state"
abbreviation "\<delta>\<^sub>w \<equiv> next_write"
abbreviation "\<delta>\<^sub>m \<equiv> next_move"

lemma M_rec[simp]: "M_rec = \<lparr> TM_record.tape_count = k, \<comment> \<open>as \<^const>\<open>TM.tape_count\<close> overwrites \<^const>\<open>TM_record.tape_count\<close>
        in \<^locale>\<open>TM\<close> contexts, it must be specified explicitly.\<close>
  symbols = \<Sigma>, states = Q, initial_state = q\<^sub>0, final_states = F, label = lab,
  next_state = \<delta>\<^sub>q, next_write = \<delta>\<^sub>w, next_move  = \<delta>\<^sub>m \<rparr>"
  unfolding TM_fields_defs by simp


text\<open>\<^bold>\<open>Tape-symbols\<close> \<open>\<Sigma>\<^sub>t\<^sub>p\<close> is the set of valid symbols that may be written or read by \<^term>\<open>M\<close>.
  This includes all \<^emph>\<open>input symbols\<close> \<^const>\<open>\<Sigma>\<close> and the \<^const>\<open>blank_symbol\<close>.\<close>

abbreviation tape_symbols where "tape_symbols \<equiv> options symbols"
abbreviation "\<Sigma>\<^sub>t\<^sub>p \<equiv> tape_symbols"
lemma tape_symbols_altdef: "\<Sigma>\<^sub>t\<^sub>p = tape_symbols_rec M_rec" unfolding symbols_def ..
lemma tape_symbols_simps[iff]: "set_option s \<subseteq> \<Sigma> \<longleftrightarrow> s \<in> \<Sigma>\<^sub>t\<^sub>p" unfolding set_options_eq ..


(* TODO document *)
definition "labels \<equiv> label ` F"

lemma in_labelsI: "q \<in> F \<Longrightarrow> label q \<in> labels" unfolding labels_def by blast
declare (in -) TM.in_labelsI[intro]

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

lemma finite_final_states: "finite F" unfolding final_states_def
  using state_axioms(3,1) by (rule finite_subset)
lemma finite_labels: "finite labels" unfolding labels_def
  using finite_final_states by (rule finite_imageI)

lemmas at_least_one_tape = at_least_one_tape[folded TM_fields_defs]
lemma at_least_one_tape': "k \<ge> 1" using at_least_one_tape unfolding One_nat_def by (fact Suc_leI)
lemmas symbol_axioms = symbol_axioms[folded TM_fields_defs]
lemmas state_axioms = state_axioms[folded TM_fields_defs] finite_final_states finite_labels
lemma transition_axioms:
  assumes "q \<in> Q" and "length hds = k" and "set hds \<subseteq> \<Sigma>\<^sub>t\<^sub>p"
  shows next_state_valid: "\<delta>\<^sub>q q hds \<in> Q"
    and next_write_valid: "i < k \<Longrightarrow> \<delta>\<^sub>w q hds i \<in> \<Sigma>\<^sub>t\<^sub>p"
  using assms unfolding TM_fields_defs by (blast intro: next_state_valid next_write_valid)+

lemmas TM_axioms[simp, intro] = at_least_one_tape at_least_one_tape' state_axioms symbol_axioms transition_axioms
lemmas (in -) TM_axioms[simp, intro] = TM.TM_axioms

lemma final_states_valid: "q \<in> F \<Longrightarrow> q \<in> Q" using state_axioms(3) by blast
declare (in -) TM.final_states_valid[dest]

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


subsubsection\<open>Usage\<close>

text\<open>The following code showcases the usage of TM concepts in this draft:\<close>

notepad
begin
  fix M M\<^sub>1 :: "('q, 's, 'l) TM"

  text\<open>The underlying record fields of a TM can be accessed using \<close>

  interpret TM M .
  term \<delta>\<^sub>q
  term next_state
  term "TM.next_state M"
  thm state_axioms

  interpret M\<^sub>1: TM M\<^sub>1 .
  term M\<^sub>1.\<delta>\<^sub>q
  term M\<^sub>1.next_state
  term "TM.next_state M\<^sub>1"
  thm M\<^sub>1.state_axioms
end


subsubsection\<open>Symbols as Type\<close>

(* TODO document, motivate *)

locale typed_TM = TM M for M :: "('q, 's::finite, 'l) TM" +
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

definition (in -) tape_size :: "'s tape \<Rightarrow> nat"
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

definition map_tape_indexed :: "(int \<Rightarrow> 'a option \<Rightarrow> 'b option) \<Rightarrow> 'a tape \<Rightarrow> 'b tape"
  where "map_tape_indexed f t \<equiv> Tape (map_indexed
         (\<lambda>n. f ((int n) - int (length (left t)))) (left t))
         (f 0 (head t)) (map_indexed
         (\<lambda>n. f ((int n) + 1)) (right t))"

definition tape_nth_aux :: "'a tape \<Rightarrow> nat \<Rightarrow> 'a option" where
  "tape_nth_aux t n \<equiv> if n < length (left t) then (left t) ! n else
                        if n = length (left t) then head t else
                        (right t) ! (n - length (left t) - 1)"

definition tape_nth :: "'a tape \<Rightarrow> int \<Rightarrow> 'a option" (infixl "!\<^sub>t" 98) where
  "t !\<^sub>t i \<equiv> if i \<ge> -int (length (left t)) \<and> i \<le> int (length (right t)) then
                tape_nth_aux t (nat (i + int (length (left t)))) else
                None"

notation (input) tape_nth (infixl "!t" 98)
notation (input) tape_nth (infixl "!T" 98)

lemma map_tape_indexed_id [simp]: "map_tape_indexed (\<lambda>_ x. x) t = t"
  unfolding map_tape_indexed_def by simp

lemma map_tape_indexed_nth [simp]: "i \<ge> -int (length (left t)) \<Longrightarrow>
       i \<le> int (length (right t)) \<Longrightarrow>
       (map_tape_indexed f t) !\<^sub>t i = f i (t !\<^sub>t i)"
  unfolding map_tape_indexed_def tape_nth_def tape_nth_aux_def apply auto
  using nat_eq_iff by fastforce

lemma map_tape_indexed_length_left [simp]:
  "length (left (map_tape_indexed f t)) = length (left t)"
  unfolding map_tape_indexed_def by simp

lemma map_tape_indexed_length_right [simp]:
  "length (right (map_tape_indexed f t)) = length (right t)"
  unfolding map_tape_indexed_def by simp

lemma tape_size_map_tape_indexed [simp]: "tape_size (map_tape_indexed f t) = tape_size t"
  unfolding tape_size_def by simp

lemma tape_nth_equalityI: "length (left t1) = length (left t2) \<Longrightarrow>
       length (right t1) = length (right t2) \<Longrightarrow>
       (\<And>i. i \<ge> -int (length (left t1)) \<Longrightarrow> i \<le> int (length (right t1)) \<Longrightarrow>
       t1 !T i = t2 !T i) \<Longrightarrow> t1 = t2"
  apply (rule tape.expand)
proof safe
  assume a1: "length (left t1) = length (left t2)" and
         a2: "length (right t1) = length (right t2)" and
         a3: "\<And>i. - int (length (left t1)) \<le> i \<Longrightarrow>
              i \<le> int (length (right t1)) \<Longrightarrow> t1 !\<^sub>t i = t2 !\<^sub>t i"
  have "\<And>n. n < length (left t1) \<Longrightarrow> (left t1) ! n = (left t2) ! n"
  proof -
    fix n :: nat
    assume a4: "n < length (left t1)"
    have 1: "tape_nth_aux t1 (nat (int n - int (length (left t1)) +
          int (length (left t1)))) = left t1 ! n"
      unfolding tape_nth_aux_def using a4 by simp
    have 2: "tape_nth_aux t2 (nat (int n - int (length (left t1)) +
          int (length (left t2)))) = left t2 ! n"
      unfolding tape_nth_aux_def using a4 a1 by simp
    note a3 [unfolded tape_nth_def, where i="int n - int (length (left t1))",
             unfolded 1 2, simplified]
    thus "left t1 ! n = left t2 ! n" using a1 a4 by auto
  qed
  from a1 this show "left t1 = left t2" by (rule nth_equalityI)
next
  assume a1: "length (left t1) = length (left t2)" and
         a2: "length (right t1) = length (right t2)" and
         a3: "\<And>i. - int (length (left t1)) \<le> i \<Longrightarrow>
              i \<le> int (length (right t1)) \<Longrightarrow> t1 !\<^sub>t i = t2 !\<^sub>t i"
  thus "head t1 = head t2" by (metis add_0 int_eq_iff less_not_refl negative_zle_0
        tape_nth_aux_def tape_nth_def)
next
  assume a1: "length (left t1) = length (left t2)" and
         a2: "length (right t1) = length (right t2)" and
         a3: "\<And>i. - int (length (left t1)) \<le> i \<Longrightarrow>
              i \<le> int (length (right t1)) \<Longrightarrow> t1 !\<^sub>t i = t2 !\<^sub>t i"
  have "\<And>n. n < length (right t1) \<Longrightarrow> (right t1) ! n = (right t2) ! n"
  proof -
    fix n :: nat
    have 1: "\<And>t. nat (int n + 1 + int (length (left t))) < length (left t) = False"
      by simp
    have 2: "\<And>t. (nat (int n + 1 + int (length (left t))) = length (left t)) = False"
      by simp
    have 3 [simp]: "\<And>t. (if int n + 1 \<le> int (length (right t))
   then if False then left t ! nat (int n + 1 + int (length (left t)))
        else if False then head t else right t ! n
   else None) = (if int n + 1 \<le> int (length (right t))
   then right t ! n else None)" by simp
    have 4: "\<And>t. nat (int n + 1 + int (length (left t))) - length (left t) - 1 = n"
      by simp
    show "n < length (right t1) \<Longrightarrow> right t1 ! n = right t2 ! n"
      using a3 [unfolded tape_nth_def tape_nth_aux_def, where i="int n + 1",
                            unfolded 1 2 4, simplified, unfolded a2]
      by (simp add: a2)
  qed
  from a2 this show "right t1 = right t2" by (rule nth_equalityI)
qed

lemma map_tape_indexed_head [simp]: "head (map_tape_indexed f t) = f 0 (head t)"
  unfolding map_tape_indexed_def by simp

lemma tape_nth_0 [simp]: "t !T 0 = head t"
  unfolding tape_nth_def tape_nth_aux_def by simp

subsubsection\<open>Configuration\<close>
                                                  
text\<open>We define a TM \<^emph>\<open>configuration\<close> as a datatype of:\<close>

datatype ('q, 's) TM_config = TM_config
  (state: 'q) \<comment> \<open>the current state\<close>
  (tapes: "'s tape list") \<comment> \<open>current contents of all tapes\<close>

text\<open>Combined with the \<^typ>\<open>('q, 's, 'l) TM\<close> definition,
  it completely describes a TM at any time during its execution.\<close>

(* helpful lemmas complementing the ones generated by datatype *)
declare TM_config.map_sel[simp]
lemmas TM_config_eq = TM_config.expand[OF conjI] (* sadly, \<open>datatype\<close> does not provide this directly (cf. \<open>some_record.equality\<close> defined by \<open>record\<close> *)

abbreviation (in TM_abbrevs) "map_conf_state f \<equiv> map_TM_config f (\<lambda>s. s)"
abbreviation (in TM_abbrevs) "map_conf_tapes f \<equiv> map_TM_config (\<lambda>q. q) f"


abbreviation (in TM) (input) "conf_label c \<equiv> label (state c)"


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

definition (in TM) is_final :: "('q, 's) TM_config \<Rightarrow> bool" where
  "is_final c \<equiv> state c \<in> F"

abbreviation (in TM) "is_not_final c \<equiv> \<not> is_final c"

mk_ide (in -) TM.is_final_def |intro is_finalI[intro]| |dest is_finalD[dest]|

lemma (in -) is_final_cong[cong]: "state c = state c' \<Longrightarrow> TM.is_final M c = TM.is_final M c'"
  by (simp add: TM.is_final_def)

lemma (in -) is_final_cong'[cong]: "state c \<in> TM.F M1 \<longleftrightarrow> state c' \<in> TM.F M2 \<Longrightarrow> TM.is_final M1 c = TM.is_final M2 c'"
  by (simp add: TM.is_final_def)


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
  unfolding wf_config_def by auto

mk_ide wf_config_iff |dest wf_configD[dest]| |elim wf_configE[elim]|
declare (in -) TM.wf_configD[dest] TM.wf_configE[elim]

lemma (in typed_TM) wf_config_def: "wf_config c \<longleftrightarrow> state c \<in> Q \<and> length (tapes c) = k"
  unfolding wf_config_def by simp

(* automation utterly fail on these two seemingly simple lemmas *)
lemma
  assumes "wf_config c"
  shows wf_config_tapes_nonempty'[dest]: "0 < length (tapes c)"
    and wf_config_tapes_nonempty[dest]: "tapes c \<noteq> []"
proof -
  from \<open>wf_config c\<close> have "length (tapes c) = k" ..
  then show "0 < length (tapes c)" by simp
  then show "tapes c \<noteq> []" by simp
qed

lemma wf_config_hd_hds_valid[dest]:
  assumes "wf_config c"
  shows "hd (heads c) \<in> \<Sigma>\<^sub>t\<^sub>p"
proof (rule set_mp)
  from \<open>wf_config c\<close> show "set (heads c) \<subseteq> \<Sigma>\<^sub>t\<^sub>p" by (rule wf_config_hds)
  from \<open>wf_config c\<close> have "heads c \<noteq> []" by blast
  then show "hd (heads c) \<in> set (heads c)" by (fact hd_in_set)
qed

lemma wf_config_hd_hds[simp]: "wf_config c \<Longrightarrow> head (hd (tapes c)) = hd (heads c)" by (force simp: hd_map)

lemma wf_config_last[dest, intro]: "wf_config c \<Longrightarrow> set_tape (last (tapes c)) \<subseteq> \<Sigma>" by auto

lemma wf_config_transferI:
  assumes "wf_config c"
    and q: "state c \<in> Q \<Longrightarrow> state (f c) \<in> TM.states M'"
    and l: "length (tapes c) = k \<Longrightarrow> length (tapes (f c)) = TM.tape_count M'"
    and s: "\<forall>tp\<in>set (tapes c). set_tape tp \<subseteq> \<Sigma> \<Longrightarrow> \<forall>tp\<in>set (tapes (f c)). set_tape tp \<subseteq> TM.symbols M'"
  shows "TM.wf_config M' (f c)"
  using \<open>wf_config c\<close>
  by (elim wf_configE) (intro TM.wf_configI q l s)

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

lemma shift_left_no_left: "\<exists>h r1 r2. tape_shift Shift_Left \<langle>|h|r1\<rangle> = \<langle>|None|r2\<rangle>"
  by simp

paragraph\<open>Write Symbols\<close>

text\<open>Write a symbol to the current position of the TM tape head.\<close>

definition tape_write :: "'s tp_symbol \<Rightarrow> 's tape \<Rightarrow> 's tape"
  where "tape_write s tp = \<langle>left tp|s|right tp\<rangle>"

corollary tape_write_simps[simp]: "tape_write s \<langle>l|h|r\<rangle> = \<langle>l|s|r\<rangle>" unfolding tape_write_def by simp
corollary tape_write_id[simp]: "tape_write (head tp) tp = tp" by (induction tp) simp
corollary tape_write_hd[simp]: "head (tape_write s tp) = s" by (induction tp) simp

lemma tape_write_id'[simp]: "i < length tps \<Longrightarrow> tape_write (map head tps ! i) (tps ! i) = (tps ! i)" by simp

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

lemma tape_action_simps[simp]:
  shows tape_action_no_write: "tape_action (head tp, m) tp = tape_shift m tp"
    and tape_action_no_write': "i < length tps \<Longrightarrow> tape_action (map head tps ! i, m) (tps ! i) = tape_shift m (tps ! i)"
    and tape_action_no_move: "tape_action (s, No_Shift) tp = tape_write s tp"
  unfolding tape_action_altdef by auto

lemma tape_action_map[simp]:
  "tape_action (map_option f s, m) (map_tape f tp) = map_tape f (tape_action (s, m) tp)"
  unfolding tape_action_def by simp

lemma tape_action_set: "set_tape (tape_action (s, m) tp) \<subseteq> set_option s \<union> set_tape tp"
  unfolding tape_action_def tape_shift_set fst_conv by (fact tape_write_set)

end \<comment> \<open>\<^locale>\<open>TM_abbrevs\<close>\<close>

definition tapes_eq_mod_shift :: "'s tape \<Rightarrow> 's tape \<Rightarrow> bool" (infix "\<simeq>\<^sub>s" 45) where
  "T1 \<simeq>\<^sub>s T2 \<equiv> (\<exists>n::nat. ((TM_abbrevs.tape_shift Shift_Left) ^^ n) T1 = T2) \<or>
               (\<exists>n::nat. ((TM_abbrevs.tape_shift Shift_Right) ^^ n) T1 = T2)"

lemma tapes_eq_mod_shift_eqI [intro, simp]: "T \<simeq>\<^sub>s T"
  unfolding tapes_eq_mod_shift_def by (meson funpow_0)

lemma tapes_eq_mod_shift_leftI [intro]:
    "((TM_abbrevs.tape_shift Shift_Left) ^^ n) T1 = T2 \<Longrightarrow>
    T1 \<simeq>\<^sub>s T2" unfolding tapes_eq_mod_shift_def by auto

lemma tapes_eq_mod_shift_rightI [intro]:
    "((TM_abbrevs.tape_shift Shift_Right) ^^ n) T1 = T2 \<Longrightarrow>
    T1 \<simeq>\<^sub>s T2" unfolding tapes_eq_mod_shift_def by auto

lemma tapes_eq_mod_shiftE [elim!]: "T1 \<simeq>\<^sub>s T2 \<Longrightarrow>
    (\<And>n. ((TM_abbrevs.tape_shift Shift_Left) ^^ n) T1 = T2 \<Longrightarrow> P) \<Longrightarrow>
    (\<And>n. ((TM_abbrevs.tape_shift Shift_Right) ^^ n) T1 = T2 \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding tapes_eq_mod_shift_def by auto

subsubsection\<open>Steps\<close>

context TM
begin

definition step_not_final :: "('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config"
  where "step_not_final c = (let q=state c; hds=heads c in TM_config
      (next_state q hds)
      (map2 tape_action (next_actions q hds) (tapes c)))"

lemma step_not_final_simps:
  shows "state (step_not_final c) = \<delta>\<^sub>q (state c) (heads c)"
    and "tapes (step_not_final c) = map2 tape_action (\<delta>\<^sub>a (state c) (heads c)) (tapes c)"
  unfolding step_not_final_def by (simp_all add: Let_def)
declare (in -) TM.step_not_final_simps[simp]

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

lemma (in -) step_not_final_eqI1:
  fixes f\<^sub>q f\<^sub>t\<^sub>p\<^sub>s
  assumes f_def: "f = (\<lambda>c. case c of TM_config q tps \<Rightarrow> TM_config (f\<^sub>q q) (f\<^sub>t\<^sub>p\<^sub>s tps))"
  assumes q: "f\<^sub>q (TM.\<delta>\<^sub>q M1 (state c) (heads c)) = TM.\<delta>\<^sub>q M2 (f\<^sub>q (state c)) (map head (f\<^sub>t\<^sub>p\<^sub>s (tapes c)))"
    and tps: "f\<^sub>t\<^sub>p\<^sub>s (tapes (TM.step_not_final M1 c)) = tapes (TM.step_not_final M2 (f c))"
  shows "f (TM.step_not_final M1 c) = TM.step_not_final M2 (f c)"
proof -
  have [simp]: "state (f c) = f\<^sub>q (state c)" "tapes (f c) = f\<^sub>t\<^sub>p\<^sub>s (tapes c)" for c by (induction c) (auto simp: f_def)
  from q tps show ?thesis by (intro TM_config_eq) auto
qed


text\<open>If the current state is not final,
  apply the action determined by \<^const>\<open>\<delta>\<close> for the current configuration.
  Otherwise, do not execute any action.\<close>
definition step :: "('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config"
  where "step c = (if state c \<in> F then c else step_not_final c)"

abbreviation "steps n \<equiv> step ^^ n"

corollary step_simps:
  shows step_final: "is_final c \<Longrightarrow> step c = c"
    and step_not_final: "\<not> is_final c \<Longrightarrow> step c = step_not_final c"
  unfolding step_def is_final_def by auto
declare (in -) TM.step_simps[simp, intro]

corollary steps_plus[simp]: "steps n2 (steps n1 c) = steps (n1 + n2) c"
  unfolding add.commute[of n1 n2] funpow_add comp_def ..

lemma stepI: "(is_final c \<Longrightarrow> P c) \<Longrightarrow> (\<not>is_final c \<Longrightarrow> P (TM.step_not_final M c)) \<Longrightarrow>
              P (TM.step M c)" unfolding TM.step_def by auto


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

lemma not_final_next_state[dest]:
  assumes "\<not> is_final (step c)"
  shows "\<delta>\<^sub>q (state c) (heads c) \<notin> F"
proof -
  from assms have "\<not> is_final c" by blast
  then have [simp]: "step c = step_not_final c" ..
  from assms show ?thesis unfolding is_final_def by simp
qed


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
lemma wf_step: "wf_config c \<Longrightarrow> wf_config (step c)" by (cases "is_final c") auto

lemma steps_l_tps: "length (tapes c) = k \<Longrightarrow> length (tapes (steps n c)) = k" using step_l_tps by (elim funpow_induct)
lemma wf_steps: "wf_config c \<Longrightarrow> wf_config (steps n c)" using wf_step by (elim funpow_induct)

declare (in -) TM.wf_step[intro] TM.wf_steps[intro]

definition symbols_in_config :: "('q, 's) TM_config \<Rightarrow> 's set" where
  "symbols_in_config c \<equiv> {s. \<exists>t\<in>set (tapes c). s \<in> set_tape t}"

lemma symbols_in_config_after_step:
  assumes "\<And>s. s \<in> symbols_in_config c \<Longrightarrow> s \<in> symbols" and
          "state c \<in> states" and
          "length (heads c) = k" and
          "s \<in> symbols_in_config (step c)"
  shows "s \<in> symbols" using assms
  unfolding step_def apply (cases "state c \<in> F")
   apply (auto simp add: step_not_final_def Let_def symbols_in_config_def)
proof (erule in_set_zipE)
  fix a and b and t
  assume a1: "\<And>s. \<exists>t\<in>set (tapes c). s \<in> set_tape t \<Longrightarrow> s \<in> \<Sigma>" and
         a2: "state c \<notin> F" and a3: "s \<in> set_tape (tape_action (a, b) t)" and
         a4: "(a, b) \<in> set (\<delta>\<^sub>a (state c) (heads c))" and a5: "t \<in> set (tapes c)" and
         a6: "state c \<in> Q" and a7: "length (tapes c) = k"
  have 1: "\<And>s t. t\<in>set (tapes c) \<Longrightarrow> s \<in> set_tape t \<Longrightarrow> s \<in> \<Sigma>"
    using a1 by blast
  have 2: "length (heads c) = k" using a7 by simp
  show "s \<in> \<Sigma>" using a2 a3 a4 a5
    apply (cases a)
     apply (cases b)
    apply auto
    using 1 apply (metis None_in_options Un_iff in_mono set_options_eq
        tape_action_set)
      using 1 apply (metis Un_empty_left in_mono set_empty_eq tape_action_set)
     using 1 apply (metis Un_empty_left in_mono set_empty_eq tape_write_set)
    apply (cases b)
      apply auto unfolding next_actions_def next_writes_def apply (erule in_set_zipE)
       apply auto unfolding tape_action_def apply auto
   proof -
     fix x :: nat
     show "state c \<notin> F \<Longrightarrow>
           s \<in> set_tape (tape_write (\<delta>\<^sub>w (state c) (heads c) x) t) \<Longrightarrow>
           t \<in> set (tapes c) \<Longrightarrow>
           Shift_Left \<in> set (next_moves (state c) (heads c)) \<Longrightarrow> x < k \<Longrightarrow> s \<in> \<Sigma>"
       apply (cases "Some s = \<delta>\<^sub>w (state c) (heads c) x")
       using next_write_valid [OF a6 2, of x] apply auto
        apply (metis Some_options_iff a1 list.set_map subset_eq tapes_heads_valid)
       by (metis 1 UnE elem_set subsetD tape_write_set)
   next
     fix x :: nat
     show "\<And>aa. state c \<notin> F \<Longrightarrow> s \<in> set_tape (tape_write (Some aa) t) \<Longrightarrow>
           (Some aa, Shift_Right) \<in> set (zip (map (\<delta>\<^sub>w (state c) (heads c)) [0..<k])
           (next_moves (state c) (heads c))) \<Longrightarrow> t \<in> set (tapes c) \<Longrightarrow>
           a = Some aa \<Longrightarrow> b = Shift_Right \<Longrightarrow> s \<in> \<Sigma>"
       apply (erule in_set_zipE) apply auto
       apply (cases "Some s = \<delta>\<^sub>w (state c) (heads c) x")
       using next_write_valid [OF a6 2, of x] apply auto
        apply (metis (no_types, lifting) 1 2 Un_iff a6 next_write_valid subset_iff
           tape_symbols_simps tape_write_set tapes_heads_valid)
       by (metis (no_types, lifting) 1 2 Un_iff a6 next_write_valid subset_iff
           tape_symbols_simps tape_write_set tapes_heads_valid)
   next
     show "\<And>aa. state c \<notin> F \<Longrightarrow> s \<in> set_tape (tape_write (Some aa) t) \<Longrightarrow>
           (Some aa, No_Shift) \<in> set (zip (map (\<delta>\<^sub>w (state c) (heads c)) [0..<k])
           (next_moves (state c) (heads c))) \<Longrightarrow> t \<in> set (tapes c) \<Longrightarrow>
           a = Some aa \<Longrightarrow> b = No_Shift \<Longrightarrow> s \<in> \<Sigma>"
       apply (erule in_set_zipE) apply auto
       by (metis (no_types, lifting) 1 2 TM.next_write_valid Un_iff a6 subset_iff
           tape_symbols_simps tape_write_set tapes_heads_valid)
   qed
qed

definition reachable_states_config :: "('q, 's) TM_config \<Rightarrow> nat \<Rightarrow> 'q set" where
  "reachable_states_config c n \<equiv> {s. \<exists>n'\<le>n. state (steps n' c) = s}"

definition reachable_symbols_config :: "('q, 's) TM_config \<Rightarrow> nat \<Rightarrow> 's set" where
  "reachable_symbols_config c n \<equiv> {s. \<exists>n'\<le>n. s \<in> (symbols_in_config (steps n' c))}"

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>

fun symbols_to_extensible :: "'s set \<Rightarrow> 's list set" where
  "symbols_to_extensible s = Collect (\<lambda>a :: 's list. length a = 1 \<and> (hd a)\<in>s)"

lemma set_ext_eq: "e\<in>s \<longleftrightarrow> [e]\<in>symbols_to_extensible s"
  by simp

lemma ext_neq:
  fixes x y :: "'a set"
  assumes "x \<noteq> y"
  shows "symbols_to_extensible x \<noteq> symbols_to_extensible y"
proof -
  let ?ex = "symbols_to_extensible x"
  let ?ey = "symbols_to_extensible y"
  have "\<exists>e. e\<in>x \<and> e\<notin>y \<or> e\<in>y \<and> e\<notin>x" using assms by blast
  hence "\<exists>e. e\<in>?ex \<and> e\<notin>?ey \<or> e\<in>?ey \<and> e\<notin>?ex" by (meson set_ext_eq)
  thus ?thesis by auto
qed

lemma ext_image: "symbols_to_extensible s = image (\<lambda>x. [x]) s"
  by (auto simp add: length_1_hd_last length_1_last_iff rev_image_eqI)

lemma ext_inj: "inj symbols_to_extensible"
  using ext_neq inj_altdef by blast

lemma ext_singletons:
  fixes e :: "'s list" and s :: "'s set"
  assumes "e\<in>symbols_to_extensible s"
  shows "length e = 1"
  using assms by auto

lemma ext_words: "w \<in> ss* \<Longrightarrow> (map (\<lambda>x. [x]) w) \<in> (symbols_to_extensible ss)*"
  by auto

fun flatten_options :: "'a list option \<Rightarrow> 'a option" where
  "flatten_options None = None" |
  "flatten_options (Some []) = None" |
  "flatten_options (Some l) = Some (hd l)"

lemma flatten_options_simp: "flatten_options (Some (h#t)) = Some h"
  by simp

lemma flatten_options_elem:
  fixes l :: "'a list option"
  assumes "l \<noteq> None" and "length (the l) \<ge> 1"
  obtains e where "flatten_options l = Some e"
  by (metis Suc_eq_plus1_left add_diff_cancel_right' assms(1) assms(2) cancel_comm_monoid_add_class.diff_cancel
      diff_is_0_eq flatten_options.simps(3) length_Cons length_append length_append_singleton list.exhaust_sel
      not_less_eq_eq option.exhaust option.sel)

lemma symbols_ext_reverse: "x\<in>ss \<Longrightarrow> \<exists>y\<in>options(symbols_to_extensible ss). y \<noteq> None \<and>
                            the (flatten_options y) = x" apply auto
  by (smt (verit, del_insts) Some_options_iff flatten_options_simp length_1_hd_iff
      list.sel(1) mem_Collect_eq option.sel)

lemma flatten_options_surj: "surj flatten_options"
proof auto
  fix x :: "'a option"
  show "x \<in> range flatten_options"
  proof (cases x)
    case None
    then show ?thesis using flatten_options.simps(1) by blast
  next
    case (Some a)
    have "\<exists>b. flatten_options b = Some a" by (metis flatten_options.simps(3) list.sel(1))
    then show ?thesis by (metis Some rangeI)
  qed
qed

lemma flatten_options_inj_on_singletons: "inj_on flatten_options {a. \<exists>b. a = Some b \<and> length b = 1}"
proof auto
  have "inj Some" by simp
  moreover have "inj_on hd {l. length l = 1}"
  proof auto
    have "\<And>x y. length x = 1 \<Longrightarrow> length y = 1 \<Longrightarrow> hd x = hd y \<Longrightarrow> x = y"
    proof -
      fix x y :: "'x list"
      assume "length x = 1" and "length y = 1" and "hd x = hd y"
      have "\<exists>e. [e] = x"
        by (metis Nil_tl One_nat_def Zero_not_Suc \<open>length x = 1\<close> diff_Suc_1 length_0_conv length_tl)
      moreover have "\<exists>e. [e] = y"
        by (metis Nil_tl One_nat_def Zero_not_Suc \<open>length y = 1\<close> diff_Suc_1 length_0_conv length_tl)
      ultimately obtain ex and ey where "[ex] = x" and "[ey] = y" by blast
      from \<open>hd x = hd y\<close> have "ex = ey" using \<open>[ex] = x\<close> \<open>[ey] = y\<close> by auto
      thus "x = y" using \<open>[ex] = x\<close> \<open>[ey] = y\<close> by auto
    qed
    thus "inj_on hd {l. length l = Suc 0}" by (metis (mono_tags, lifting) One_nat_def inj_onI mem_Collect_eq)
  qed
  ultimately show "inj_on flatten_options {Some b |b. length b = Suc 0}"
    by (smt (verit) One_nat_def flatten_options.elims injD inj_onD inj_onI mem_Collect_eq option.distinct(1))
qed

fun tm_to_ext_tm :: "('a, 'b, 'c) TM \<Rightarrow> ('a, 'b list, 'c) TM_record" where
  "tm_to_ext_tm tm = TM (TM.tape_count tm) (symbols_to_extensible (TM.symbols tm)) (TM.states tm) (TM.initial_state tm)
                     (TM.final_states tm) (TM.label tm)
                     (\<lambda>a :: 'a. (\<lambda>b :: 'b list option list. TM.next_state tm a (map flatten_options b)))
                     (\<lambda>a :: 'a. (\<lambda>b :: 'b list option list.
                     (\<lambda>n :: nat. map_option (\<lambda>x. [x]) (TM.next_write tm a (map (flatten_options) b) n))))
                     (\<lambda>a :: 'a. (\<lambda>b :: 'b list option list. TM.next_move tm a (map (flatten_options) b)))"

lemma ext_tape_count: "tape_count (tm_to_ext_tm tm) = TM.tape_count tm" by simp
lemma ext_symbols: "[s] \<in> (symbols (tm_to_ext_tm tm)) \<longleftrightarrow> s \<in> (TM.symbols tm)" by simp
lemma ext_states: "states (tm_to_ext_tm tm) = TM.states tm" by simp
lemma ext_initial_state: "initial_state (tm_to_ext_tm tm) = TM.initial_state tm" by simp
lemma ext_final_states: "final_states (tm_to_ext_tm tm) = TM.final_states tm" by simp
lemma ext_label: "label (tm_to_ext_tm tm) = TM.label tm" by simp
lemma ext_next_state: "next_state (tm_to_ext_tm tm) a b = TM.next_state tm a (map (flatten_options) b)" by simp
lemma ext_next_write: "next_write (tm_to_ext_tm tm) a b n =
                              map_option (\<lambda>x. [x]) (TM.next_write tm a (map (flatten_options) b) n)" by simp
lemma ext_next_move: "next_move (tm_to_ext_tm tm) a b = TM.next_move tm a (map (flatten_options) b)" by simp

lemma ext_symbol_length: "s\<in>symbols (tm_to_ext_tm tm) \<Longrightarrow> length s = 1" by simp

lemma valid_tm_tape_count: "valid_TM tm \<Longrightarrow> TM.tape_count (Abs_TM tm) = tape_count tm"
  unfolding TM.tape_count_def by (simp add: Abs_TM_inverse)
lemma valid_tm_symbols: "valid_TM tm \<Longrightarrow> TM.symbols (Abs_TM tm) = symbols tm"
  unfolding TM.symbols_def by (simp add: Abs_TM_inverse)
lemma valid_tm_states: "valid_TM tm \<Longrightarrow> TM.states (Abs_TM tm) = states tm"
  unfolding TM.states_def by (simp add: Abs_TM_inverse)
lemma valid_tm_initial_state: "valid_TM tm \<Longrightarrow> TM.initial_state (Abs_TM tm) = initial_state tm"
  unfolding TM.initial_state_def by (simp add: Abs_TM_inverse)
lemma valid_tm_final_states: "valid_TM tm \<Longrightarrow> TM.final_states (Abs_TM tm) = final_states tm"
  unfolding TM.final_states_def by (simp add: Abs_TM_inverse)
lemma valid_tm_label: "valid_TM tm \<Longrightarrow> TM.label (Abs_TM tm) = label tm"
  unfolding TM.label_def by (simp add: Abs_TM_inverse)
lemma valid_tm_next_state: "valid_TM tm \<Longrightarrow> TM.next_state (Abs_TM tm) = next_state tm"
  unfolding TM.next_state_def by (simp add: Abs_TM_inverse)
lemma valid_tm_next_write: "valid_TM tm \<Longrightarrow> TM.next_write (Abs_TM tm) = next_write tm"
  unfolding TM.next_write_def by (simp add: Abs_TM_inverse)
lemma valid_tm_next_move: "valid_TM tm \<Longrightarrow> TM.next_move (Abs_TM tm) = next_move tm"
  unfolding TM.next_move_def by (simp add: Abs_TM_inverse)

lemma ext_tm_valid: "valid_TM (tm_to_ext_tm tm)"
proof
  show "0 < tape_count (tm_to_ext_tm tm)" by simp
next
  show "finite (symbols (tm_to_ext_tm tm))"
  proof auto
    let ?list_set = "{a. (hd a) \<in> TM.TM.symbols tm \<and> length a = 1}"
    have "finite (TM.TM.symbols tm)" by simp
    moreover have "\<exists>f. bij_betw f (TM.TM.symbols tm) ?list_set"
    proof -
      define f :: "'b \<Rightarrow> 'b list" where "f \<equiv> \<lambda>b. [b]"
      have "\<And>x. hd (f x) = x" by (simp add: \<open>f \<equiv> \<lambda>b. [b]\<close>)
      hence "inj f" by (metis injI)
      have "\<And>x. f (hd x) = [hd x]" by (simp add: \<open>f \<equiv> \<lambda>b. [b]\<close>)
      have "\<And>x. length x = 1 \<longleftrightarrow> (\<exists>y. x = [y])" by (metis One_nat_def Suc_length_conv length_0_conv)
      hence "\<And>y. y\<in>?list_set \<Longrightarrow> f (hd y) = y"
        by (metis (mono_tags, lifting) \<open>f \<equiv> \<lambda>b. [b]\<close> hd_Cons_tl list.distinct(1) mem_Collect_eq tl_Nil)
      hence "bij_betw f (TM.TM.symbols tm) ?list_set"
        by (smt (verit, best) \<open>\<And>x. (length x = 1) = (\<exists>y. x = [y])\<close> \<open>\<And>x. hd (f x) = x\<close> \<open>f \<equiv> \<lambda>b. [b]\<close> bij_betwI' mem_Collect_eq)
      thus "\<exists>f. bij_betw f (TM.TM.symbols tm) ?list_set" by auto
    qed
    ultimately show "finite {a. length a = Suc 0 \<and> hd a \<in> TM.TM.symbols tm}"
      by (metis (no_types, lifting) Collect_cong One_nat_def bij_betw_finite)
  qed
next
  have "TM.symbols tm \<noteq> {}" by simp
  thus "symbols (tm_to_ext_tm tm) \<noteq> {}"
  proof auto
    obtain x where "x\<in>TM.TM.symbols tm" by fastforce
    let ?y = "[x]"
    have "length ?y = 1" by simp
    moreover have "hd ?y \<in> TM.TM.symbols tm" by (simp add: \<open>x \<in> TM.TM.symbols tm\<close>)
    ultimately show "\<exists>x. length x = Suc 0 \<and> hd x \<in> TM.TM.symbols tm" by (metis One_nat_def)
  qed
next
  show "finite (states (tm_to_ext_tm tm))" by simp
next
  show "initial_state (tm_to_ext_tm tm) \<in> states (tm_to_ext_tm tm)" by simp
next
  show "final_states (tm_to_ext_tm tm) \<subseteq> states (tm_to_ext_tm tm)" by simp
next
  fix q hds
  show "q \<in> states (tm_to_ext_tm tm) \<Longrightarrow>
       wf_hds_rec (tm_to_ext_tm tm) hds \<Longrightarrow> next_state (tm_to_ext_tm tm) q hds \<in> states (tm_to_ext_tm tm)"
  proof auto
    let ?list_set = "{a. length a = Suc 0 \<and> (hd a) \<in> TM.TM.symbols tm}"
    assume "q \<in> TM.TM.states tm" and "length hds = TM.TM.tape_count tm"
    and "set hds \<subseteq> options ?list_set"
    have "\<And>s. None\<in>options s" ..
    moreover have "\<And>x. x\<in>set hds \<Longrightarrow> x\<in>options (symbols_to_extensible (TM.TM.symbols tm))"
      using \<open>set hds \<subseteq> options ?list_set\<close> by auto
    moreover have "\<And>x. x\<in>set(map flatten_options hds) \<Longrightarrow> x \<noteq> None \<Longrightarrow> Some [the x]\<in>set hds"
    proof auto
      fix xa y
      assume "xa \<in> set hds" and "flatten_options xa = Some y"
      obtain sxa where "xa = Some sxa"
        using \<open>flatten_options xa = Some y\<close> by fastforce
      have "length sxa = 1"
        using \<open>xa = Some sxa\<close> \<open>xa \<in> set hds\<close> calculation(2) by fastforce
      hence "[hd sxa] = sxa"
        by (metis diff_is_0_eq' le_numeral_extra(4) length_0_conv length_greater_0_conv length_tl less_one
             list.distinct(1) list.expand list.sel(1) list.sel(3))
      thus "Some [y] \<in> set hds"
        by (metis \<open>flatten_options xa = Some y\<close> \<open>xa = Some sxa\<close> \<open>xa \<in> set hds\<close> flatten_options.simps(3) option.inject)
    qed
    ultimately have "\<And>x. x\<in>set(map flatten_options hds) \<Longrightarrow> x\<in>options(TM.symbols tm)"
      by (metis Some_options_iff option.collapse set_ext_eq)
    hence "set (map flatten_options hds) \<subseteq> options (TM.symbols tm)" by auto
    thus "TM.TM.next_state tm q (map flatten_options hds) \<in> TM.TM.states tm"
      by (simp add: \<open>length hds = TM.TM.tape_count tm\<close> \<open>q \<in> TM.TM.states tm\<close>)
  qed
next
  fix q hds i
  show "q \<in> states (tm_to_ext_tm tm) \<Longrightarrow>
       wf_hds_rec (tm_to_ext_tm tm) hds \<Longrightarrow>
       i < tape_count (tm_to_ext_tm tm) \<Longrightarrow> next_write (tm_to_ext_tm tm) q hds i \<in> tape_symbols_rec (tm_to_ext_tm tm)"
  proof auto
    let ?list_set = "{a. length a = Suc 0 \<and> hd a \<in> TM.TM.symbols tm}"
    assume 1: "q \<in> TM.TM.states tm" and 2: "i < TM.TM.tape_count tm" and 3: "length hds = TM.TM.tape_count tm"
    and 4: "set hds \<subseteq> options ?list_set"
    have "\<And>s. None\<in>options s" ..
    moreover have "(TM.TM.next_write tm q (map flatten_options hds) i) \<noteq> None \<Longrightarrow>
    the (TM.TM.next_write tm q (map flatten_options hds) i) \<in> TM.TM.symbols tm"
    proof auto
      fix y
      assume 5: "TM.TM.next_write tm q (map flatten_options hds) i = Some y"
      moreover have "\<And>x. Some x\<in>options ?list_set \<Longrightarrow> Some (hd x)\<in>options (TM.TM.symbols tm)" by simp
      moreover have "set (map flatten_options hds) \<subseteq> options (TM.TM.symbols tm)"
      proof -
         have "\<And>s. None\<in>options s" ..
    moreover have "\<And>x. x\<in>set hds \<Longrightarrow> x\<in>options (symbols_to_extensible (TM.TM.symbols tm))"
      using \<open>set hds \<subseteq> options ?list_set\<close> by auto
    moreover have "\<And>x. x\<in>set(map flatten_options hds) \<Longrightarrow> x \<noteq> None \<Longrightarrow> Some [the x]\<in>set hds"
      proof auto
        fix xa y
        assume "xa \<in> set hds" and "flatten_options xa = Some y"
        obtain sxa where "xa = Some sxa"
          using \<open>flatten_options xa = Some y\<close> by fastforce
        have "length sxa = 1"
          using \<open>xa = Some sxa\<close> \<open>xa \<in> set hds\<close> calculation(2) by fastforce
        hence "[hd sxa] = sxa"
          by (metis diff_is_0_eq' le_numeral_extra(4) length_0_conv length_greater_0_conv length_tl less_one
             list.distinct(1) list.expand list.sel(1) list.sel(3))
        thus "Some [y] \<in> set hds"
          by (metis \<open>flatten_options xa = Some y\<close> \<open>xa = Some sxa\<close> \<open>xa \<in> set hds\<close> flatten_options.simps(3) option.inject)
      qed
    ultimately have "\<And>x. x\<in>set(map flatten_options hds) \<Longrightarrow> x\<in>options(TM.symbols tm)"
      by (metis Some_options_iff option.collapse set_ext_eq)
    thus "set (map flatten_options hds) \<subseteq> options (TM.TM.symbols tm)" by auto
      qed
      ultimately show "y \<in> TM.TM.symbols tm"
        by (metis (no_types, lifting) 1 2 3 Some_options_iff TM.next_write_valid length_map)
    qed
    moreover have "\<And>a. a = None \<or> (\<exists>x. a = Some x)" by auto
    moreover have "\<And>a s. a\<in>s \<Longrightarrow> (map_option (\<lambda>x. [x]) (Some a)) \<in> options (symbols_to_extensible s)" by simp
    moreover have "?list_set = symbols_to_extensible (TM.TM.symbols tm)" by simp
    ultimately show "map_option (\<lambda>x. [x]) (TM.TM.next_write tm q (map flatten_options hds) i) \<in> options ?list_set"
      by (smt (verit, best) None_eq_map_option_iff option.collapse)
  qed
qed

fun tm_tape_ext :: "'s tape \<Rightarrow> 's list tape" where
  "tm_tape_ext (Tape l h r) = Tape (map (\<lambda>x. (map_option (\<lambda>xo. [xo]) x)) l) (map_option (\<lambda>xo. [xo]) h)
    (map (\<lambda>x. (map_option (\<lambda>xo. [xo]) x)) r)"

lemma head_always_length_1 [intro, simp]:
    "head (tm_tape_ext t) \<noteq> None \<Longrightarrow> length (the (head (tm_tape_ext t))) = 1"
  by (induction t) auto

lemma tape_shift_ext: "tm_tape_ext (TM_abbrevs.tape_shift a tp) = TM_abbrevs.tape_shift a (tm_tape_ext tp)"
proof (cases a; auto)
  case Shift_Left
  show "tm_tape_ext (TM_abbrevs.tape_shift Shift_Left tp) = TM_abbrevs.tape_shift Shift_Left (tm_tape_ext tp)"
    by (metis TM_abbrevs.tape_shift_map tape.exhaust_sel tape.map tm_tape_ext.simps)
next
  case Shift_Right
  show "tm_tape_ext (TM_abbrevs.tape_shift Shift_Right tp) = TM_abbrevs.tape_shift Shift_Right (tm_tape_ext tp)"
    by (metis TM_abbrevs.tape_shift_map tape.exhaust_sel tape.map tm_tape_ext.simps)
next
  case No_Shift
  then show "tm_tape_ext (TM_abbrevs.tape_shift No_Shift tp) = TM_abbrevs.tape_shift No_Shift (tm_tape_ext tp)"
    by (simp add: TM_abbrevs.tape_shift.simps(5))
qed

lemma tape_write_ext: "tm_tape_ext (TM_abbrevs.tape_write a tp) =
                       TM_abbrevs.tape_write (map_option (\<lambda>x. [x]) a) (tm_tape_ext tp)"
  by (metis TM_abbrevs.map_tape_def TM_abbrevs.tape_write_map tape.exhaust_sel tm_tape_ext.simps)

lemma next_writes_ext: "map (\<lambda>x. (map_option (\<lambda>y. [y])) x) (TM.next_writes tm q (map (flatten_options) hds)) =
                        TM.next_writes (Abs_TM (tm_to_ext_tm tm)) q hds"
  apply (unfold TM.next_writes_def)
proof -
  have "\<And>n. map_option (\<lambda>y. [y]) (TM.TM.next_write tm q (map flatten_options hds) n) =
        TM.TM.next_write (Abs_TM (tm_to_ext_tm tm)) q hds n"
    by (metis ext_next_write ext_tm_valid valid_tm_next_write)
  moreover have "[0..<TM.TM.tape_count tm] = [0..<TM.TM.tape_count (Abs_TM (tm_to_ext_tm tm))]"
    by (metis ext_tape_count ext_tm_valid valid_tm_tape_count)
  ultimately show "map (map_option (\<lambda>y. [y])) (map (TM.TM.next_write tm q (map flatten_options hds))
    [0..<TM.TM.tape_count tm]) =
    map (TM.TM.next_write (Abs_TM (tm_to_ext_tm tm)) q hds) [0..<TM.TM.tape_count (Abs_TM (tm_to_ext_tm tm))]"
      by simp
  qed

lemma flatten_unflatten_id [simp]: "flatten_options \<circ> map_option (\<lambda>y. [y]) = (\<lambda>x. x)"
proof
  have 1: "(flatten_options \<circ> map_option (\<lambda>y. [y])) None = None" by simp
  moreover have 2: "\<And>x. (flatten_options \<circ> map_option (\<lambda>y. [y])) (Some x) = (Some x)" by simp
  ultimately show "\<And>x. (flatten_options \<circ> map_option (\<lambda>y. [y])) x = x"
    apply (insert 1 2) apply (erule option.induct) by simp
qed

lemma tm_ext_step_state [simp]:
  fixes tm :: "('a, 'b, 'c) TM" and tmc :: "('a, 'b) TM_config" and tmc_ext :: "('a, 'b list) TM_config"
  assumes "state tmc_ext = state tmc" and "tapes tmc_ext = map tm_tape_ext (tapes tmc)"
  shows "state (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext) = state (TM.step tm tmc)"
proof -
  let ?tm_ext = "tm_to_ext_tm tm"
  have "\<And>l. map (flatten_options) (map (\<lambda>x. map_option (\<lambda>y. [y]) x) l) = l" by auto
  moreover have "next_state ?tm_ext (state tmc_ext) (heads tmc_ext) =
                 TM.next_state tm (state tmc) (map (flatten_options) (heads tmc_ext))"
    using assms(1) by fastforce
  ultimately have "\<And>s b. TM.TM.next_state tm s b = next_state ?tm_ext s (map (\<lambda>x. map_option (\<lambda>y. [y]) x) b)" by simp
  have 6:"\<And>q tm tmc. q = state tmc \<Longrightarrow> q\<in>TM.F tm \<Longrightarrow> state (TM.step tm tmc) = state tmc" by (simp add: TM.step_def)
  moreover have "\<And>q tm. q = state tmc_ext \<Longrightarrow> q\<in>TM.F tm \<Longrightarrow> state (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext) = state tmc_ext"
  proof safe
    have "\<And>tm q. q \<in> TM.F tm \<longleftrightarrow> q \<in> final_states (tm_to_ext_tm tm)" by simp
    hence "\<And>tm q. q \<in> TM.F tm \<longleftrightarrow> q \<in> TM.F (Abs_TM (tm_to_ext_tm tm))"
      by (metis ext_tm_valid valid_tm_final_states)
    thus "\<And>tm. state tmc_ext \<in> TM.F tm \<Longrightarrow> state (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext) = state tmc_ext"
      by (metis calculation)
  qed
  ultimately have 7: "\<And>q tm. q = state tmc \<Longrightarrow> q\<in>TM.F tm \<Longrightarrow> state (TM.step tm tmc) =
                  state (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext)" by (metis assms(1))
  have "\<And>tm. TM.next_state tm (state tmc) (heads tmc) = next_state (tm_to_ext_tm tm) (state tmc_ext) (heads tmc_ext)"
  proof auto
    have "\<And>t. (head \<circ> tm_tape_ext) t = ((map_option (\<lambda>x. [x])) \<circ> head) t"
      by (metis TM_abbrevs.map_tape_def comp_apply tape.collapse tape.map_sel(2) tm_tape_ext.simps)
    hence "map (flatten_options \<circ> (head \<circ> tm_tape_ext)) (tapes tmc) =
          map (flatten_options \<circ> (map_option (\<lambda>x. [x]) \<circ> head)) (tapes tmc)" by metis
    also have "... = map (flatten_options \<circ> (map_option (\<lambda>x. [x])) \<circ> head) (tapes tmc)"
      by (metis comp_assoc)
    ultimately have "map (flatten_options \<circ> head \<circ> tm_tape_ext) (tapes tmc) = heads tmc" by simp
    hence "map (flatten_options \<circ> head) (tapes tmc_ext) = heads tmc"
      by (simp add: assms(2))
    thus "\<And>tm. TM.TM.next_state tm (state tmc) (heads tmc) =
          TM.TM.next_state tm (state tmc_ext) (map (flatten_options \<circ> head) (tapes tmc_ext))"
      by (simp add: assms(1))
  qed
  hence 8: "\<And>tm. state tmc \<notin> TM.F tm \<Longrightarrow>
          state (TM.step_not_final tm tmc) = state (TM.step_not_final (Abs_TM (tm_to_ext_tm tm)) tmc_ext)"
    by (metis Abs_TM_inverse TM.TM.next_state_def TM.step_not_final_simps(1) ext_tm_valid mem_Collect_eq)
  hence "state tmc \<notin> TM.F tm \<Longrightarrow> state (TM.step tm tmc) =
                  state (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext)"
  proof -
    assume "state tmc \<notin> TM.F tm"
    have "TM.F tm = final_states (tm_to_ext_tm tm)" by simp
    hence "TM.F tm = TM.F (Abs_TM (tm_to_ext_tm tm))"
      by (metis ext_tm_valid valid_tm_final_states)
    hence "state tmc_ext \<notin> TM.F (Abs_TM (tm_to_ext_tm tm))"
      by (simp add: \<open>state tmc \<notin> TM.TM.final_states tm\<close> assms(1))
    hence "state (TM.step tm tmc) = state (TM.step_not_final tm tmc)"
      by (simp add: TM.step_def \<open>state tmc \<notin> TM.F tm\<close>)
    also have "... = state (TM.step_not_final (Abs_TM (tm_to_ext_tm tm)) tmc_ext)"
      using 8 \<open>state tmc \<notin> TM.F tm\<close> by auto
    also have "... = state (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext)"
      by (metis TM.step_def \<open>state tmc_ext \<notin> TM.TM.final_states (Abs_TM (tm_to_ext_tm tm))\<close>)
    ultimately show "state (TM.step tm tmc) = state (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext)" by simp
  qed
  from 7 this show ?thesis by metis
qed

lemma tm_ext_step_tapes:
  fixes tm :: "('a, 'b, 'c) TM" and tmc :: "('a, 'b) TM_config" and tmc_ext :: "('a, 'b list) TM_config"
  assumes "state tmc_ext = state tmc" and "tapes tmc_ext = map tm_tape_ext (tapes tmc)"
  shows "tapes (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext) = map tm_tape_ext (tapes (TM.step tm tmc))"
proof -
  have "\<And>tm tmc. state tmc \<in> TM.F tm \<Longrightarrow> TM.step tm tmc = tmc" by auto
  hence "state tmc \<in> TM.F tm \<Longrightarrow> tapes (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext) = map tm_tape_ext (tapes (TM.step tm tmc))"
  proof -
    assume a1: "state tmc \<in> TM.TM.final_states tm" and
    a2: "\<And>tmc tm. state tmc \<in> TM.TM.final_states tm \<Longrightarrow> TM.step tm tmc = tmc"
    hence "TM.step tm tmc = tmc" by auto
    have "state tmc_ext \<in> TM.TM.final_states (Abs_TM (tm_to_ext_tm tm))"
      by (metis a1 assms(1) ext_final_states ext_tm_valid valid_tm_final_states)
    hence "TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext = tmc_ext" by auto
    thus "tapes (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext) = map tm_tape_ext (tapes (TM.step tm tmc))"
      using \<open>TM.step tm tmc = tmc\<close> assms(2) by presburger
  qed
  moreover have "state tmc \<notin> TM.F tm \<Longrightarrow>
      tapes (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext) = map tm_tape_ext (tapes (TM.step tm tmc))"
  proof -
    assume "state tmc \<notin> TM.F tm"
    have 1: "[0..<TM.TM.tape_count (Abs_TM (tm_to_ext_tm tm))] = [0..<TM.TM.tape_count tm]"
      by (metis ext_tape_count ext_tm_valid valid_tm_tape_count)
    have "tapes (TM.step_not_final (Abs_TM (tm_to_ext_tm tm)) tmc_ext) =
          map tm_tape_ext (tapes (TM.step_not_final tm tmc))" apply (simp add: assms del: tm_to_ext_tm.simps)
      apply (unfold TM.next_actions_def)
    proof -
      have 2: "map (head \<circ> tm_tape_ext) (tapes tmc) = map (\<lambda>x. map_option (\<lambda>y. [y]) x) (heads tmc)"
        by auto (metis TM_abbrevs.tape_write_hd TM_abbrevs.tape_write_id tape_write_ext)
      moreover have "\<And>x. x \<noteq> None \<Longrightarrow> \<exists>e. Some [e] = map_option (\<lambda>y. [y]) x" by auto
      hence 3: "map flatten_options (map (\<lambda>x. map_option (\<lambda>y. [y]) x) (heads tmc)) = heads tmc"
        by auto (metis (full_types) flatten_options.simps(1) flatten_options_simp
            not_Some_eq option.simps(8) option.simps(9))
      ultimately have "TM.next_writes (Abs_TM (tm_to_ext_tm tm)) (state tmc) (map (head \<circ> tm_tape_ext) (tapes tmc)) =
            map (\<lambda>x. map_option (\<lambda>y. [y]) x) (TM.next_writes tm (state tmc) (heads tmc))"
        by (metis next_writes_ext)
      moreover have 4: "TM.next_moves (Abs_TM (tm_to_ext_tm tm)) (state tmc) (map (head \<circ> tm_tape_ext) (tapes tmc)) =
                     TM.next_moves tm (state tmc) (heads tmc)"
        by (metis TM.next_moves_def 1 2 3 ext_next_move ext_tm_valid valid_tm_next_move)
      ultimately show "map2 TM_abbrevs.tape_action
     (zip (TM.next_writes (Abs_TM (tm_to_ext_tm tm)) (state tmc) (map (head \<circ> tm_tape_ext) (tapes tmc)))
       (TM.next_moves (Abs_TM (tm_to_ext_tm tm)) (state tmc) (map (head \<circ> tm_tape_ext) (tapes tmc))))
     (map tm_tape_ext (tapes tmc)) =
    map (tm_tape_ext \<circ> (\<lambda>(x, y). TM_abbrevs.tape_action x y))
     (zip (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (tapes tmc))"
         apply (simp add: 4 del: tm_to_ext_tm.simps)
      proof -
        have 5: "map (tm_tape_ext \<circ> (\<lambda>(x, y). TM_abbrevs.tape_action x y))
     (zip (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (tapes tmc)) =
              map tm_tape_ext (map2 TM_abbrevs.tape_action
      (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (tapes tmc))"
          by simp
        moreover have "map2 TM_abbrevs.tape_action
     (zip (map (map_option (\<lambda>y. [y])) (TM.next_writes tm (state tmc) (heads tmc)))
       (TM.next_moves tm (state tmc) (heads tmc)))
     (map tm_tape_ext (tapes tmc)) = map tm_tape_ext (map2 TM_abbrevs.tape_action
      (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (tapes tmc))"
          apply (unfold TM_abbrevs.tape_action_def)
        proof auto
          have "map (tm_tape_ext \<circ> (\<lambda>(x, y). TM_abbrevs.tape_shift (snd x) (TM_abbrevs.tape_write (fst x) y)))
     (zip (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (tapes tmc)) =
                map (\<lambda>(x, y). TM_abbrevs.tape_shift (snd x) (tm_tape_ext (TM_abbrevs.tape_write (fst x) y)))
     (zip (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (tapes tmc))"
            by (simp add: case_prod_unfold tape_shift_ext)
          also have "... = map (\<lambda>(x, y). TM_abbrevs.tape_shift (snd x) (TM_abbrevs.tape_write (map_option (\<lambda>x. [x]) (fst x)) (tm_tape_ext y)))
     (zip (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (tapes tmc))"
            by (simp add: tape_write_ext)
          also have "... = map (\<lambda>(x, y). TM_abbrevs.tape_shift (snd x) (TM_abbrevs.tape_write (map_option (\<lambda>x. [x]) (fst x)) y))
     (zip (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (map tm_tape_ext (tapes tmc)))"
            by (metis (no_types, lifting) case_prod_conv map2_cong map_zip_map2)
          also have "... = map (\<lambda>((x1, x2), y). TM_abbrevs.tape_shift (snd ((map_option (\<lambda>x. [x]) x1), x2)) (TM_abbrevs.tape_write (fst ((map_option (\<lambda>x. [x]) x1), x2)) y))
     (zip (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (map tm_tape_ext (tapes tmc)))"
            by auto
          also have "... = map (\<lambda>(x, y). TM_abbrevs.tape_shift (snd x) (TM_abbrevs.tape_write (fst x) y))
     (map (\<lambda>((x11, x12), x2). ((map_option (\<lambda>y. [y]) x11, x12), x2)) (zip (zip (TM.next_writes tm (state tmc) (heads tmc))
       (TM.next_moves tm (state tmc) (heads tmc)))
     (map tm_tape_ext (tapes tmc))))" by auto
          also have "... = map (\<lambda>(x, y). TM_abbrevs.tape_shift (snd x) (TM_abbrevs.tape_write (fst x) y))
     (zip (map (\<lambda>(x1, x2). (map_option (\<lambda>y. [y]) x1, x2)) (zip (TM.next_writes tm (state tmc) (heads tmc))
       (TM.next_moves tm (state tmc) (heads tmc))))
     (map tm_tape_ext (tapes tmc)))"
            by (smt (verit, ccfv_SIG) cond_case_prod_eta old.prod.case zip_map1)
          also have "... = map (\<lambda>(x, y). TM_abbrevs.tape_shift (snd x) (TM_abbrevs.tape_write (fst x) y))
     (zip (zip (map (map_option (\<lambda>y. [y])) (TM.next_writes tm (state tmc) (heads tmc)))
       (TM.next_moves tm (state tmc) (heads tmc)))
     (map tm_tape_ext (tapes tmc)))"
            by (simp add: zip_map1)
          finally show "map2 (\<lambda>x y. TM_abbrevs.tape_shift (snd x) (TM_abbrevs.tape_write (fst x) y))
     (zip (map (map_option (\<lambda>y. [y])) (TM.next_writes tm (state tmc) (heads tmc)))
       (TM.next_moves tm (state tmc) (heads tmc)))
     (map tm_tape_ext (tapes tmc)) =
    map (tm_tape_ext \<circ> (\<lambda>(x, y). TM_abbrevs.tape_shift (snd x) (TM_abbrevs.tape_write (fst x) y)))
     (zip (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (tapes tmc))"
            by auto
        qed
        ultimately show "map2 TM_abbrevs.tape_action
     (zip (map (map_option (\<lambda>y. [y])) (TM.next_writes tm (state tmc) (heads tmc)))
       (TM.next_moves tm (state tmc) (heads tmc)))
     (map tm_tape_ext (tapes tmc)) =
    map (tm_tape_ext \<circ> (\<lambda>(x, y). TM_abbrevs.tape_action x y))
     (zip (zip (TM.next_writes tm (state tmc) (heads tmc)) (TM.next_moves tm (state tmc) (heads tmc))) (tapes tmc))"
          by simp
      qed
    qed
    thus "tapes (TM.step (Abs_TM (tm_to_ext_tm tm)) tmc_ext) = map tm_tape_ext (tapes (TM.step tm tmc))"
      apply (unfold TM.step_def)
      using \<open>state tmc \<notin> TM.TM.final_states tm\<close> assms(1) ext_tm_valid valid_tm_final_states by force
  qed
  ultimately show ?thesis by auto
qed

lemma tm_ext_steps_eq:
  fixes tm :: "('a, 'b, 'c) TM" and tmc :: "('a, 'b) TM_config" and tmc_ext :: "('a, 'b list) TM_config"
  assumes "state tmc_ext = state tmc" and "tapes tmc_ext = map tm_tape_ext (tapes tmc)"
  shows "state (TM.steps (Abs_TM (tm_to_ext_tm tm)) n tmc_ext) = state (TM.steps tm n tmc)"
        (is "state ?c1 = state ?c2") and
    "tapes (TM.steps (Abs_TM (tm_to_ext_tm tm)) n tmc_ext) = map tm_tape_ext (tapes (TM.steps tm n tmc))"
    (is "tapes ?c1 = map ?f (tapes ?c2)")
proof -
  have "state ?c1 = state ?c2 \<and> tapes ?c1 = map ?f (tapes ?c2)"
  proof (induct n)
    case 0
    then show ?case by (simp add: assms)
  next
    case (Suc n)
    have f1 [simp]: "state ((TM.step (Abs_TM (tm_to_ext_tm tm)) ^^ n) tmc_ext) = state ((TM.step tm ^^ n) tmc)" using Suc by blast
    have f2: "tapes ((TM.step (Abs_TM (tm_to_ext_tm tm)) ^^ n) tmc_ext) = map tm_tape_ext (tapes ((TM.step tm ^^ n) tmc))"
      using Suc by blast
    have "state (TM.step (Abs_TM (tm_to_ext_tm tm)) ((TM.step (Abs_TM (tm_to_ext_tm tm)) ^^ n) tmc_ext)) =
          state (TM.step tm ((TM.step tm ^^ n) tmc))" using f1 f2 tm_ext_step_state by blast
    moreover have "tapes (TM.step (Abs_TM (tm_to_ext_tm tm)) ((TM.step (Abs_TM (tm_to_ext_tm tm)) ^^ n) tmc_ext)) =
          map tm_tape_ext (tapes (TM.step tm ((TM.step tm ^^ n) tmc)))" using f1 f2 tm_ext_step_tapes by blast
    ultimately have "state ((TM.step (Abs_TM (tm_to_ext_tm tm)) ^^ Suc n) tmc_ext) = state ((TM.step tm ^^ Suc n) tmc)"
      and "tapes ((TM.step (Abs_TM (tm_to_ext_tm tm)) ^^ Suc n) tmc_ext) =
          map tm_tape_ext (tapes ((TM.step tm ^^ Suc n) tmc))" by simp_all
    then show ?case ..
  qed
  thus "state ?c1 = state ?c2" and "tapes ?c1 = map ?f (tapes ?c2)" by simp_all
qed

lemma no_shift_tape_symbol: "TM.next_move tm (state c) (heads c) n = No_Shift \<Longrightarrow>
                 state c \<notin> TM.F tm \<Longrightarrow> n < TM.tape_count tm \<Longrightarrow> n < length (tapes c) \<Longrightarrow>
                 head ((tapes (TM.step tm c)) ! n) =
                 TM.next_write tm (state c) (heads c) n"
proof (induct c)
  case (TM_config s t)
  then show ?case unfolding TM.step_def apply auto
  proof (rule map2_subst)
    assume "n < TM.TM.tape_count tm" and "n < length t"
    thus "n < length (TM.next_actions tm s (map head t))"
      by (simp add: TM.next_actions_simps(2))
  next
    show "n < length t \<Longrightarrow> n < length t" .
  next
    assume a1: "TM.TM.next_move tm s (map head t) n = No_Shift" and
           "s \<notin> TM.TM.final_states tm" and
           "n < TM.TM.tape_count tm" and "n < length t"
    thus "head (TM_abbrevs.tape_action (TM.next_actions tm s (map head t)!n) (t!n)) =
    TM.TM.next_write tm s (map head t) n" unfolding TM.next_actions_def
      TM.next_writes_def TM.next_moves_def TM_abbrevs.tape_action_def apply auto
      unfolding a1
      by (simp add: TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_hd)
  qed
qed

lemma tape_count_step_equal: "TM.tape_count tm \<ge> length (tapes tmc) \<Longrightarrow>
       length (tapes (((TM.step tm) ^^ n) tmc)) = length (tapes tmc)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  moreover have "\<And>tmc. TM.tape_count tm \<ge> length (tapes tmc) \<Longrightarrow>
                 length (tapes ((TM.step tm tmc))) = length (tapes tmc)"
    unfolding TM.step_def TM.step_not_final_def
  proof (auto, unfold Let_def)
    fix tmc :: "('b, 'a) TM_config"
    assume "state tmc \<notin> TM.TM.final_states tm" and
      "length (tapes tmc) \<le> TM.TM.tape_count tm"
    thus "length
            (tapes
              (TM_config (TM.TM.next_state tm (state tmc) (heads tmc))
               (map2 TM_abbrevs.tape_action (TM.next_actions tm (state tmc) (heads tmc))
                  (tapes tmc)))) = length (tapes tmc)"
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def
        TM.next_writes_def TM.next_moves_def by auto
  qed
  ultimately show ?case by simp
qed

lemma no_move_same_write_same_tps: "TM.next_move tm (state c) (heads c) n = No_Shift \<Longrightarrow>
       TM.next_write tm (state c) (heads c) n = (heads c) ! n \<Longrightarrow>
       n < TM.tape_count tm \<Longrightarrow> n < length (tapes c) \<Longrightarrow>
       tapes (TM.step tm c) ! n = tapes c ! n"
  unfolding TM.step_def by (simp add: TM.next_actions_simps(1)
      TM.next_actions_simps(2) TM_abbrevs.tape_action_no_move TM_abbrevs.tape_write_id)

lemma no_move_same_right: "TM.next_move tm (state c) (heads c) n = No_Shift \<Longrightarrow>
                           n < TM.tape_count tm \<Longrightarrow> n < length (tapes c) \<Longrightarrow>
                           right (tapes (TM.step tm c) ! n) = right (tapes c ! n)"
  unfolding TM.step_def apply auto unfolding TM.next_actions_def
    TM_abbrevs.tape_action_def TM.next_moves_def apply (rule map2_subst)
  apply auto
   apply (simp add: TM.next_writes_simps(2))
proof -
  assume a1: "TM.TM.next_move tm (state c) (heads c) n = No_Shift" and
         "n < TM.TM.tape_count tm" and "n < length (tapes c)" and
         "state c \<notin> TM.TM.final_states tm"
  hence 1: "snd (zip (TM.next_writes tm (state c) (heads c))
              (map (TM.TM.next_move tm (state c) (heads c)) [0..<TM.TM.tape_count tm]) !
             n) =
        (TM.TM.next_move tm (state c) (heads c)) n"
    by (simp add: TM.next_writes_simps(2))
    have 2: "fst (zip (TM.next_writes tm (state c) (heads c))
                (map (TM.TM.next_move tm (state c) (heads c)) [0..<TM.TM.tape_count tm]) !
               n) = TM.next_write tm (state c) (heads c) n"
      by (metis TM.next_actions_def TM.next_actions_simps(1) TM.next_moves_def
          \<open>n < TM.TM.tape_count tm\<close> fstI)
  show "right (TM_abbrevs.tape_shift (snd (zip (TM.next_writes tm (state c) (heads c))
        (map (TM.TM.next_move tm (state c) (heads c)) [0..<TM.TM.tape_count tm]) ! n))
       (TM_abbrevs.tape_write
         (fst (zip (TM.next_writes tm (state c) (heads c))
          (map (TM.TM.next_move tm (state c) (heads c)) [0..<TM.TM.tape_count tm]) ! n))
         (tapes c ! n))) = right (tapes c ! n)" unfolding 1 2 a1
    by (simp add: TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_def)
qed

lemma no_move_same_left: "TM.next_move tm (state c) (heads c) n = No_Shift \<Longrightarrow>
                           n < TM.tape_count tm \<Longrightarrow> n < length (tapes c) \<Longrightarrow>
                           left (tapes (TM.step tm c) ! n) = left (tapes c ! n)"
unfolding TM.step_def apply auto unfolding TM.next_actions_def
    TM_abbrevs.tape_action_def TM.next_moves_def apply (rule map2_subst)
  apply auto
   apply (simp add: TM.next_writes_simps(2))
proof -
  assume a1: "TM.TM.next_move tm (state c) (heads c) n = No_Shift" and
         "n < TM.TM.tape_count tm" and "n < length (tapes c)" and
         "state c \<notin> TM.TM.final_states tm"
  hence 1: "snd (zip (TM.next_writes tm (state c) (heads c))
              (map (TM.TM.next_move tm (state c) (heads c)) [0..<TM.TM.tape_count tm]) !
             n) =
        (TM.TM.next_move tm (state c) (heads c)) n"
    by (simp add: TM.next_writes_simps(2))
    have 2: "fst (zip (TM.next_writes tm (state c) (heads c))
                (map (TM.TM.next_move tm (state c) (heads c)) [0..<TM.TM.tape_count tm]) !
               n) = TM.next_write tm (state c) (heads c) n"
      by (metis TM.next_actions_def TM.next_actions_simps(1) TM.next_moves_def
          \<open>n < TM.TM.tape_count tm\<close> fstI)
  show "left (TM_abbrevs.tape_shift (snd (zip (TM.next_writes tm (state c) (heads c))
        (map (TM.TM.next_move tm (state c) (heads c)) [0..<TM.TM.tape_count tm]) ! n))
       (TM_abbrevs.tape_write
         (fst (zip (TM.next_writes tm (state c) (heads c))
          (map (TM.TM.next_move tm (state c) (heads c)) [0..<TM.TM.tape_count tm]) ! n))
         (tapes c ! n))) = left (tapes c ! n)" unfolding 1 2 a1
    by (simp add: TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_def)
qed

lemma tapes_step_left_not_empty:
  fixes tm :: "('q, 's, 'l) TM" and tmc :: "('q, 's) TM_config" and n :: nat and
        s :: "'s option"
  assumes "TM.next_write tm (state tmc) (heads tmc) n = s" and
          "TM.next_move tm (state tmc) (heads tmc) n = Shift_Left" and
          "\<not>TM.is_final tm tmc" and "n < TM.tape_count tm" and "n < length (tapes tmc)"
          and "left (tapes tmc ! n) \<noteq> []"
        shows "tapes (TM.step tm tmc) ! n =
               Tape (tl (left (tapes tmc ! n))) (hd (left (tapes tmc ! n)))
               (s#(right (tapes tmc ! n)))"
  using assms(3) unfolding TM.step_def TM.is_final_def TM.step_not_final_def
    TM.next_actions_def TM.next_writes_def Let_def apply auto
    apply (rule map2_subst) using assms(4, 5)
    apply (auto simp add: TM.next_moves_simps(2)) unfolding TM_abbrevs.tape_action_def
  TM.next_moves_def TM.next_writes_def assms(1) apply auto unfolding assms(2)
proof -
  have 1: "\<And>t. TM_abbrevs.tape_write s t = Tape (left t) s (right t)"
    using TM_abbrevs.tape_write_def .
  show "TM_abbrevs.tape_shift Shift_Left (TM_abbrevs.tape_write s (tapes tmc ! n)) =
    Tape (tl (left (tapes tmc ! n))) (hd (left (tapes tmc ! n)))
     (s # right (tapes tmc ! n))" unfolding 1 using assms(6)
    by (metis TM_abbrevs.tape_shift.simps(2) list.collapse)
qed

lemma tapes_step_left_empty:
  fixes tm :: "('q, 's, 'l) TM" and tmc :: "('q, 's) TM_config" and n :: nat and
        s :: "'s option" and l r :: "'s option list"
  assumes "TM.next_write tm (state tmc) (heads tmc) n = s" and
          "TM.next_move tm (state tmc) (heads tmc) n = Shift_Left" and
          "\<not>TM.is_final tm tmc" and "n < TM.tape_count tm" and "n < length (tapes tmc)"
          and "left (tapes tmc ! n) = []" and "l = tl (left (tapes tmc ! n))" and
          "r = s#(right (tapes tmc ! n))"
        shows "tapes (TM.step tm tmc) ! n =
               Tape l None r"
  using assms(3) unfolding TM.step_def TM.is_final_def TM.step_not_final_def
    TM.next_actions_def TM.next_writes_def Let_def apply auto
    apply (rule map2_subst) using assms(4, 5)
    apply (auto simp add: TM.next_moves_simps(2)) unfolding TM_abbrevs.tape_action_def
  TM.next_moves_def TM.next_writes_def assms(1) apply auto unfolding assms(2)
proof -
  have 1: "\<And>t. TM_abbrevs.tape_write s t = Tape (left t) s (right t)"
    using TM_abbrevs.tape_write_def .
  show "TM_abbrevs.tape_shift Shift_Left (TM_abbrevs.tape_write s (tapes tmc ! n)) =
    Tape l None r" unfolding 1 using assms
    by (simp add: TM_abbrevs.tape_shift.simps(1))
qed

lemma same_tps_shift_write:
  fixes tm1 tm2 :: "('a, 'b, 'c) TM" and tmc1 tmc2 :: "('a, 'b) TM_config"
  assumes "tapes tmc1 = tapes tmc2" and
          "\<And>k. TM.next_write tm1 (state tmc1) (heads tmc1) k =
                TM.next_write tm2 (state tmc2) (heads tmc2) k" and
          "\<And>k. TM.next_move tm1 (state tmc1) (heads tmc1) k =
                TM.next_move tm2 (state tmc2) (heads tmc2) k" and
          "TM.is_final tm1 tmc1 \<longleftrightarrow> TM.is_final tm2 tmc2" and
          "TM.TM.tape_count tm1 = TM.TM.tape_count tm2" and
          "TM.TM.tape_count tm1 = length (tapes tmc1)"
  shows "tapes (TM.step tm1 tmc1) = tapes (TM.step tm2 tmc2)"
proof -
  have "TM.is_final tm1 tmc1 \<Longrightarrow> tapes (TM.step tm1 tmc1) = tapes (TM.step tm2 tmc2)"
    using assms(1, 4) unfolding TM.step_def by auto
  moreover have "\<not>TM.is_final tm1 tmc1 \<Longrightarrow>
                 tapes (TM.step tm1 tmc1) = tapes (TM.step tm2 tmc2)"
    using assms(4) unfolding TM.step_def apply auto
    unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
              TM.next_moves_def unfolding assms(2, 3, 5, 6) unfolding assms(1) ..
  ultimately show ?thesis by blast
qed

lemma same_tps_shift_write2:
  fixes tm1 tm2 :: "('a, 'b, 'c) TM" and tmc1 tmc2 :: "('a, 'b) TM_config"
  assumes "tapes tmc1 = tapes tmc2" and
          "\<And>k. k < TM.TM.tape_count tm1 \<Longrightarrow>
                TM.next_write tm1 (state tmc1) (heads tmc1) k =
                TM.next_write tm2 (state tmc2) (heads tmc2) k" and
          "\<And>k. k < TM.TM.tape_count tm2 \<Longrightarrow>
                TM.next_move tm1 (state tmc1) (heads tmc1) k =
                TM.next_move tm2 (state tmc2) (heads tmc2) k" and
          "TM.is_final tm1 tmc1 \<longleftrightarrow> TM.is_final tm2 tmc2" and
          "TM.TM.tape_count tm1 = TM.TM.tape_count tm2" and
          "TM.TM.tape_count tm1 = length (tapes tmc1)"
  shows "tapes (TM.step tm1 tmc1) = tapes (TM.step tm2 tmc2)"
proof -
  have 1: "map (TM.TM.next_write tm1 (state tmc1) (heads tmc1))
           [0..<TM.tape_count tm2] =
           map (TM.TM.next_write tm2 (state tmc2) (heads tmc2)) [0..<TM.tape_count tm2]"
    by (simp add: assms(2, 5))
  have 2: "map (TM.TM.next_move tm1 (state tmc1) (heads tmc1))
           [0..<TM.TM.tape_count tm2] =
           map (TM.TM.next_move tm2 (state tmc2) (heads tmc2))
           [0..<TM.TM.tape_count tm2]" by (simp add: assms(3))
  have "TM.is_final tm1 tmc1 \<Longrightarrow> tapes (TM.step tm1 tmc1) = tapes (TM.step tm2 tmc2)"
    using assms(1, 4) unfolding TM.step_def by auto
  moreover have "\<not>TM.is_final tm1 tmc1 \<Longrightarrow>
                 tapes (TM.step tm1 tmc1) = tapes (TM.step tm2 tmc2)"
    using assms(4) unfolding TM.step_def apply auto
    unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
              TM.next_moves_def unfolding assms(5, 6) 1 2 unfolding assms(1) ..
  ultimately show ?thesis by blast
qed

lemma tape_shift_id_right [simp]:
      "(TM_abbrevs.tape_shift shift) \<circ> (TM_abbrevs.tape_shift No_Shift) =
       (TM_abbrevs.tape_shift shift)"
  by (metis TM_abbrevs.tape_shift.simps(5) comp_id eq_id_iff)

lemma tape_shift_id_left [simp]:
      "(TM_abbrevs.tape_shift No_Shift) \<circ> (TM_abbrevs.tape_shift shift) =
       (TM_abbrevs.tape_shift shift)"
  by (simp add: TM_abbrevs.tape_shift.simps(5) fun.map_ident_strong)
                              
lemma tps_same_write_left_no_shift:
  fixes tm1 tm2 :: "('a, 'b, 'c) TM" and tmc1 tmc2 :: "('a, 'b) TM_config"
  assumes "tapes tmc1 = tapes tmc2" and
          "\<And>k. TM.next_write tm1 (state tmc1) (heads tmc1) k =
                TM.next_write tm2 (state tmc2) (heads tmc2) k" and
          "\<And>k. TM.next_move tm1 (state tmc1) (heads tmc1) k = Shift_Left" and
          "\<And>k. TM.next_move tm2 (state tmc2) (heads tmc2) k = No_Shift"
          "\<not>TM.is_final tm1 tmc1" and "\<not>TM.is_final tm2 tmc2"
          "TM.TM.tape_count tm1 = TM.TM.tape_count tm2" and
          "TM.TM.tape_count tm1 = length (tapes tmc1)"
        shows "tapes (TM.step tm1 tmc1) =
               (map (TM_abbrevs.tape_shift Shift_Left) (tapes (TM.step tm2 tmc2)))"
  unfolding TM.step_def using assms(5, 6) unfolding TM.is_final_def apply auto
  unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
    TM.next_moves_def assms(2, 3, 4) assms(7) [symmetric] assms(8)
    map_replicate_trivial unfolding assms(1)
proof -
  have 1: "\<And>shift. map (\<lambda>(a, tp). TM_abbrevs.tape_shift (snd a)
                (TM_abbrevs.tape_write (fst a) tp))
                (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
           [0..<length (tapes tmc2)]) (shift \<up> length (tapes tmc2))) (tapes tmc2)) =
    map (\<lambda>(a, tp). TM_abbrevs.tape_shift shift (TM_abbrevs.tape_write (fst a) tp))
                (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
           [0..<length (tapes tmc2)]) (shift \<up> length (tapes tmc2))) (tapes tmc2))"
    apply auto by (metis in_set_replicate in_set_zipE)
  have 2: "map (TM_abbrevs.tape_shift Shift_Left \<circ>
         (\<lambda>(a, tp). TM_abbrevs.tape_shift (snd a) (TM_abbrevs.tape_write (fst a) tp)))
     (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
                 [0..<length (tapes tmc2)])
            (No_Shift \<up> length (tapes tmc2)))
       (tapes tmc2)) = map (TM_abbrevs.tape_shift Shift_Left)
      (map (\<lambda>(a, tp). TM_abbrevs.tape_shift (snd a) (TM_abbrevs.tape_write (fst a) tp))
     (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
                 [0..<length (tapes tmc2)])
            (No_Shift \<up> length (tapes tmc2))) (tapes tmc2)))" by simp
  have 3: "map (TM_abbrevs.tape_shift Shift_Left \<circ>
         (\<lambda>(a, tp). TM_abbrevs.tape_shift (snd a) (TM_abbrevs.tape_write (fst a) tp)))
     (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
                 [0..<length (tapes tmc2)])
            (No_Shift \<up> length (tapes tmc2)))
       (tapes tmc2)) = map (\<lambda>(a, tp). ((TM_abbrevs.tape_shift Shift_Left) \<circ>
      (TM_abbrevs.tape_shift No_Shift))
       (TM_abbrevs.tape_write (fst a) tp))
                (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
           [0..<length (tapes tmc2)]) (No_Shift \<up> length (tapes tmc2))) (tapes tmc2))"
    apply (subst (2) assms(1) [symmetric])
    by (smt (verit, best) 1 assms(1) case_prod_unfold comp_def map_equality_iff)
  show "map2 (\<lambda>x y. TM_abbrevs.tape_shift (snd x) (TM_abbrevs.tape_write (fst x) y))
   (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2)) [0..<length (tapes tmc2)])
       (Shift_Left \<up> length (tapes tmc2)))
     (tapes tmc2) =
    map (TM_abbrevs.tape_shift Shift_Left \<circ>
         (\<lambda>(a, tp). TM_abbrevs.tape_shift (snd a) (TM_abbrevs.tape_write (fst a) tp)))
     (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
                 [0..<length (tapes tmc2)])
            (No_Shift \<up> length (tapes tmc2)))
       (tapes tmc2))" unfolding 3 assms(1) 1 by (auto simp add: map_equality_iff)
qed

lemma tps_same_write_left_no_shift2:
  fixes tm1 tm2 :: "('a, 'b, 'c) TM" and tmc1 tmc2 :: "('a, 'b) TM_config"
  assumes "tapes tmc1 = tapes tmc2" and
          "\<And>k. k < TM.tape_count tm1 \<Longrightarrow> TM.next_write tm1 (state tmc1) (heads tmc1) k =
                TM.next_write tm2 (state tmc2) (heads tmc2) k" and
          "\<And>k. k < TM.tape_count tm2 \<Longrightarrow> TM.next_move tm1 (state tmc1) (heads tmc1) k =
           Shift_Left" and
          "\<And>k. TM.next_move tm2 (state tmc2) (heads tmc2) k = No_Shift"
          "\<not>TM.is_final tm1 tmc1" and "\<not>TM.is_final tm2 tmc2"
          "TM.TM.tape_count tm1 = TM.TM.tape_count tm2" and
          "TM.TM.tape_count tm1 = length (tapes tmc1)"
        shows "tapes (TM.step tm1 tmc1) =
               (map (TM_abbrevs.tape_shift Shift_Left) (tapes (TM.step tm2 tmc2)))"
  unfolding TM.step_def using assms(5, 6) unfolding TM.is_final_def apply auto
  unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
    TM.next_moves_def assms(4) assms(7) [symmetric] assms(8)
    map_replicate_trivial unfolding assms(1)
proof -
  have next_write_eq: "map (TM.TM.next_write tm1 (state tmc1) (heads tmc2))
                       [0..<length (tapes tmc2)] =
                       map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
                       [0..<length (tapes tmc2)]"
    using assms(1) assms(2) assms(8) by auto
  have next_move_1_left: "map (TM.TM.next_move tm1 (state tmc1) (heads tmc2))
                          [0..<length (tapes tmc2)] =
                          replicate (length (tapes tmc2)) Shift_Left"
    by (metis assms(1) assms(3) assms(7) assms(8) length_replicate map_nthI
        nth_replicate)
  have 1: "\<And>shift. map (\<lambda>(a, tp). TM_abbrevs.tape_shift (snd a)
                (TM_abbrevs.tape_write (fst a) tp))
                (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
           [0..<length (tapes tmc2)]) (shift \<up> length (tapes tmc2))) (tapes tmc2)) =
    map (\<lambda>(a, tp). TM_abbrevs.tape_shift shift (TM_abbrevs.tape_write (fst a) tp))
                (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
           [0..<length (tapes tmc2)]) (shift \<up> length (tapes tmc2))) (tapes tmc2))"
    apply auto by (metis in_set_replicate in_set_zipE)
  have 2: "map (TM_abbrevs.tape_shift Shift_Left \<circ>
         (\<lambda>(a, tp). TM_abbrevs.tape_shift (snd a) (TM_abbrevs.tape_write (fst a) tp)))
     (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
                 [0..<length (tapes tmc2)])
            (No_Shift \<up> length (tapes tmc2)))
       (tapes tmc2)) = map (TM_abbrevs.tape_shift Shift_Left)
      (map (\<lambda>(a, tp). TM_abbrevs.tape_shift (snd a) (TM_abbrevs.tape_write (fst a) tp))
     (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
                 [0..<length (tapes tmc2)])
            (No_Shift \<up> length (tapes tmc2))) (tapes tmc2)))" by simp
  show "map2 (\<lambda>x y. TM_abbrevs.tape_shift (snd x) (TM_abbrevs.tape_write (fst x) y))
   (zip (map (TM.TM.next_write tm1 (state tmc1) (heads tmc2)) [0..<length (tapes tmc2)])
       (map (TM.TM.next_move tm1 (state tmc1) (heads tmc2)) [0..<length (tapes tmc2)]))
     (tapes tmc2) =
    map (TM_abbrevs.tape_shift Shift_Left \<circ>
         (\<lambda>(a, tp). TM_abbrevs.tape_shift (snd a) (TM_abbrevs.tape_write (fst a) tp)))
     (zip (zip (map (TM.TM.next_write tm2 (state tmc2) (heads tmc2))
                 [0..<length (tapes tmc2)])
            (No_Shift \<up> length (tapes tmc2)))
       (tapes tmc2))" unfolding next_write_eq next_move_1_left 1 2
    by (simp add: TM_abbrevs.tape_shift.simps(5) map_equality_iff)
qed

lemma head_in_left_tape [dest]: "left tape \<noteq> [] \<Longrightarrow>
       head (TM_abbrevs.tape_shift Shift_Left tape) \<in> set (left tape)"
  by (metis TM_abbrevs.tape_shift.simps(2) list.set_intros(1) neq_Nil_conv
      tape.exhaust tape.sel(1) tape.sel(2))

lemma head_in_right_tape [dest]: "right tape \<noteq> [] \<Longrightarrow>
      head (TM_abbrevs.tape_shift Shift_Right tape) \<in> set (right tape)"
  by (metis TM_abbrevs.tape_shift.simps(4) list.set_intros(1) neq_Nil_conv tape.sel(2)
      tape.sel(3) tm_tape_ext.cases)

lemma head_left_empty [simp]: "left tape = [] \<Longrightarrow>
      head (TM_abbrevs.tape_shift Shift_Left tape) = None"
  by (metis TM_abbrevs.tape_shift.simps(1) tape.exhaust_sel tape.sel(2))

lemma head_right_empty [simp]: "right tape = [] \<Longrightarrow>
      head (TM_abbrevs.tape_shift Shift_Right tape) = None"
  by (metis TM_abbrevs.tape_shift.simps(3) tape.collapse tape.sel(2))

lemma length_left_Shift_Left: "i < TM.tape_count M \<Longrightarrow> i < length (tapes c) \<Longrightarrow>
       TM.next_move M (state c) (heads c) i = Shift_Left \<Longrightarrow> \<not>TM.is_final M c \<Longrightarrow>
       length (left (tapes (TM.step M c) ! i)) = length (left (tapes c ! i)) - 1"
  by (metis (no_types, lifting) length_tl tape.sel(1) tapes_step_left_empty
      tapes_step_left_not_empty)

lemma length_right_Shift_Left: "i < TM.tape_count M \<Longrightarrow> i < length (tapes c) \<Longrightarrow>
       TM.next_move M (state c) (heads c) i = Shift_Left \<Longrightarrow> \<not>TM.is_final M c \<Longrightarrow>
       length (right (tapes (TM.step M c) ! i)) = length (right (tapes c ! i)) + 1"
  by (metis (no_types, lifting) One_nat_def list.size(4) tape.sel(3)
      tapes_step_left_empty tapes_step_left_not_empty)

lemma length_left_Shift_Right: "i < TM.tape_count M \<Longrightarrow> i < length (tapes c) \<Longrightarrow>
       TM.next_move M (state c) (heads c) i = Shift_Right \<Longrightarrow> \<not>TM.is_final M c \<Longrightarrow>
       length (left (tapes (TM.step M c) ! i)) = length (left (tapes c ! i)) + 1"
  unfolding TM.step_def apply auto apply (rule nth_map2 [THEN ssubst])
    apply (auto simp add: TM.next_actions_simps(2))
  unfolding TM.next_actions_def TM.next_moves_def TM.next_writes_def apply auto
  unfolding TM_abbrevs.tape_action_def apply auto
  apply (cases "TM_abbrevs.tape_write (TM.TM.next_write M (state c) (heads c) i)
           (tapes c ! i)")
proof auto
  fix x1 x3 and x2
  show "i < TM.TM.tape_count M \<Longrightarrow>
       i < length (tapes c) \<Longrightarrow>
       TM.TM.next_move M (state c) (heads c) i = Shift_Right \<Longrightarrow>
       \<not> TM.is_final M c \<Longrightarrow>
       state c \<notin> TM.TM.final_states M \<Longrightarrow>
       TM_abbrevs.tape_write (TM.TM.next_write M (state c) (heads c) i) (tapes c ! i) =
       Tape x1 x2 x3 \<Longrightarrow>
       length (left (TM_abbrevs.tape_shift Shift_Right (Tape x1 x2 x3))) =
       Suc (length (left (tapes c ! i)))" apply (cases x3)
     apply auto
     apply (rule TM_abbrevs.tape_shift.simps(3) [where ls=x1 and h=x2, THEN ssubst])
     apply (simp add: TM_abbrevs.tape_write_def)
    apply (rule TM_abbrevs.tape_shift.simps(4) [where ls=x1 and h=x2, THEN ssubst])
    by (simp add: TM_abbrevs.tape_write_def)
qed

lemma length_right_Shift_Right: "i < TM.tape_count M \<Longrightarrow> i < length (tapes c) \<Longrightarrow>
       TM.next_move M (state c) (heads c) i = Shift_Right \<Longrightarrow> \<not>TM.is_final M c \<Longrightarrow>
       length (right (tapes (TM.step M c) ! i)) = length (right (tapes c ! i)) - 1"
  unfolding TM.step_def apply auto apply (rule nth_map2 [THEN ssubst])
    apply (auto simp add: TM.next_actions_simps(2))
  unfolding TM.next_actions_def TM.next_moves_def TM.next_writes_def apply auto
  unfolding TM_abbrevs.tape_action_def apply auto
  apply (cases "TM_abbrevs.tape_write (TM.TM.next_write M (state c) (heads c) i)
           (tapes c ! i)")
proof auto
  fix x1 x3 and x2
  show "i < TM.TM.tape_count M \<Longrightarrow>
       i < length (tapes c) \<Longrightarrow>
       TM.TM.next_move M (state c) (heads c) i = Shift_Right \<Longrightarrow>
       \<not> TM.is_final M c \<Longrightarrow>
       state c \<notin> TM.TM.final_states M \<Longrightarrow>
       TM_abbrevs.tape_write (TM.TM.next_write M (state c) (heads c) i) (tapes c ! i) =
       Tape x1 x2 x3 \<Longrightarrow>
       length (right (TM_abbrevs.tape_shift Shift_Right (Tape x1 x2 x3))) =
       length (right (tapes c ! i)) - Suc 0" apply (cases x3)
    by (auto simp add: TM_abbrevs.tape_shift.simps(3) TM_abbrevs.tape_write_def
        TM_abbrevs.tape_shift.simps(4))
qed

lemma no_final_states_step_not_final: "TM.final_states M = {} \<Longrightarrow>
  TM.step M c = TM.step_not_final M c"
  by blast

lemma heads_of_next_step_Right: "k < length (tapes c) \<Longrightarrow> k < TM.tape_count M \<Longrightarrow>
       right (tapes c ! k) \<noteq> [] \<Longrightarrow>
       TM.next_move M (state c) (heads c) k = Shift_Right \<Longrightarrow> \<not>TM.is_final M c \<Longrightarrow>
       heads (TM.step M c) ! k = right (tapes c ! k) ! 0"
  unfolding TM.step_def apply auto unfolding TM.next_actions_def TM.next_writes_def
    TM.next_moves_def apply auto unfolding TM_abbrevs.tape_action_def apply auto
  apply (cases "TM_abbrevs.tape_write (TM.TM.next_write M (state c) (heads c) k)
    (tapes c ! k)") apply auto
  by (metis TM_abbrevs.tape_shift.simps(4) TM_abbrevs.tape_write_def list.exhaust_sel
      nth_Cons_0 tape.sel(2))

lemma heads_of_next_step_Left: "k < length (tapes c) \<Longrightarrow> k < TM.tape_count M \<Longrightarrow>
       left (tapes c ! k) \<noteq> [] \<Longrightarrow>
       TM.next_move M (state c) (heads c) k = Shift_Left \<Longrightarrow> \<not>TM.is_final M c \<Longrightarrow>
       heads (TM.step M c) ! k = left (tapes c ! k) ! 0"
  unfolding TM.step_def apply auto unfolding TM.next_actions_def TM.next_writes_def
    TM.next_moves_def apply auto unfolding TM_abbrevs.tape_action_def apply auto
  apply (cases "TM_abbrevs.tape_write (TM.TM.next_write M (state c) (heads c) k)
    (tapes c ! k)") apply auto
  by (metis TM_abbrevs.tape_shift.simps(2) TM_abbrevs.tape_write_def list.exhaust
      nth_Cons_0 tape.sel(2))

lemma Shift_Right_is_right_not_empty: "right t \<noteq> [] \<Longrightarrow>
    head (TM_abbrevs.tape_shift Shift_Right t) = hd (right t)"
  apply (cases t)
  apply auto
  by (metis TM_abbrevs.tape_shift.simps(4) starts_with_hd tape.sel(2))

lemma Shift_Left_is_left_not_empty: "left t \<noteq> [] \<Longrightarrow>
    head (TM_abbrevs.tape_shift Shift_Left t) = hd (left t)"
  apply (cases t)
  apply auto
  by (metis TM_abbrevs.tape_shift.simps(2) starts_with_hd tape.sel(2))

lemma left_after_write [simp]: "left (TM_abbrevs.tape_write w t) = left t"
  by (simp add: TM_abbrevs.tape_write_def)

lemma right_after_write [simp]: "right (TM_abbrevs.tape_write w t) = right t"
  by (simp add: TM_abbrevs.tape_write_def)

lemma right_Shift_Right [simp]: "right (TM_abbrevs.tape_shift Shift_Right t) =
                                 tl (right t)"
  apply (cases t)
  apply auto
  by (metis TM_abbrevs.tape_shift.simps(3,4) list.exhaust list.sel(2,3) tape.sel(3))

lemma right_Shift_Left [simp]: "right (TM_abbrevs.tape_shift Shift_Left t) =
                                (head t)#right t"
  apply (cases t)
proof auto
  fix x1 x3 :: "'a option list" and x2 :: "'a option"
  show "right (TM_abbrevs.tape_shift Shift_Left (Tape x1 x2 x3)) = x2 # x3"
    apply (cases x3)
    apply auto
    by (metis TM_abbrevs.tape_shift.simps(1) TM_abbrevs.tape_shift.simps(2)
        neq_Nil_conv tape.sel(3))+
qed

lemma left_Shift_Right [simp]: "left (TM_abbrevs.tape_shift Shift_Right t) =
                                (head t)#left t"
  apply (cases t)
proof auto
  fix x1 x3 :: "'a option list" and x2 :: "'a option"
  show "left (TM_abbrevs.tape_shift Shift_Right (Tape x1 x2 x3)) = x2 # x1"
    apply (induction x3)
     apply (cases x1)
    apply (simp_all add: TM_abbrevs.tape_shift.simps(3))
    by (simp add: TM_abbrevs.tape_shift.simps(4))
qed

lemma left_Shift_Left [simp]: "left (TM_abbrevs.tape_shift Shift_Left t) =
                               tl (left t)"
  apply (cases t)
  apply auto
  by (metis TM_abbrevs.tape_shift.simps(1) TM_abbrevs.tape_shift.simps(2)
      list.sel(3) neq_Nil_conv tape.sel(1) tl_Nil)

lemma right_empty_after_Shift_Right: "i < length (tapes c) \<Longrightarrow> i < TM.tape_count M \<Longrightarrow>
       right (tapes c ! i) = [] \<Longrightarrow> TM.next_move M (state c) (heads c) i =
       Shift_Right \<Longrightarrow> right (tapes (TM.step M c) ! i) = []"
  unfolding TM.step_def apply auto apply (rule nth_map2 [THEN ssubst]) apply auto
  unfolding TM.next_actions_def TM.next_moves_def TM.next_writes_def apply auto
  unfolding TM_abbrevs.tape_action_def by simp

lemma right_empty_after_Shift_Left: "i < length (tapes c) \<Longrightarrow> i < TM.tape_count M \<Longrightarrow>
       left (tapes c ! i) = [] \<Longrightarrow> TM.next_move M (state c) (heads c) i =
       Shift_Left \<Longrightarrow> left (tapes (TM.step M c) ! i) = []"
  unfolding TM.step_def apply auto apply (rule nth_map2 [THEN ssubst]) apply auto
  unfolding TM.next_actions_def TM.next_moves_def TM.next_writes_def apply auto
  unfolding TM_abbrevs.tape_action_def by simp

lemma length_left_upper_bound:
  assumes "length (tapes c) = TM.tape_count M" and
          "i < TM.tape_count M"
        shows "length (left (tapes (TM.steps M n c) ! i)) \<le> length (left (tapes c ! i)) + n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case apply simp
    apply (subst TM.step_def)
    apply auto
    apply (rule map2_subst)
    using assms apply (simp add: TM.next_actions_simps(2))
    using assms apply (simp add: TM.steps_l_tps)
    unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def
    apply (rule zip_subst)
    using assms apply (simp_all add: TM.next_writes_simps(2))
    apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n) c))
                  (heads ((TM.step M ^^ n) c)) i")
      apply auto
    by (simp add: TM_abbrevs.tape_shift.simps(5))
qed

lemma length_left_lower_bound:
  assumes "length (tapes c) = TM.tape_count M" and
          "i < TM.tape_count M"
        shows "length (left (tapes (TM.steps M n c) ! i)) \<ge> length (left (tapes c ! i)) - n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case apply simp
    apply (subst TM.step_def)
    apply auto
    apply (rule map2_subst)
    using assms apply (simp add: TM.next_actions_simps(2))
    using assms apply (simp add: TM.steps_l_tps)
    unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def
    apply (rule zip_subst)
    using assms apply (simp_all add: TM.next_writes_simps(2))
    apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n) c))
                  (heads ((TM.step M ^^ n) c)) i")
      apply auto
    by (simp add: TM_abbrevs.tape_shift.simps(5))
qed

lemma head_shift_left_SomeD: "head (TM_abbrevs.tape_shift Shift_Left t) = Some y \<Longrightarrow>
                              left t \<noteq> []"
  by auto

lemma head_shift_right_SomeD: "head (TM_abbrevs.tape_shift Shift_Right t) = Some y \<Longrightarrow>
                               right t \<noteq> []"
  by auto
end
