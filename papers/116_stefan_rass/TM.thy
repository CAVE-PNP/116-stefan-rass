section\<open>A Theory of Turing Machines\<close>

theory TM
  imports Main "Supplementary/Misc" "Supplementary/Lists" "Supplementary/Option_S"
    "Intro_Dest_Elim.IHOL_IDE" "HOL-Library.Countable_Set"
begin


subsection\<open>Prerequisites\<close>

text\<open>We introduce the locale \<open>TM_abbrevs\<close> to scope local abbreviations.
  This allows easy access to notation without introducing possible bloat on the global scope.
  In other words, users of this theory have to \<^emph>\<open>opt-in\<close> to more specialized abbreviations.
  The idea for this is from the Style Guide for Contributors to IsarMathLib\<^footnote>\<open>\<^url>\<open>https://www.nongnu.org/isarmathlib/IsarMathLib/CONTRIBUTING.html\<close>\<close>.\<close>
locale TM_abbrevs

(* TODO consider extracting these to some other theory *)
type_synonym ('symbol) word = "'symbol list"
type_synonym ('symbol) lang = "'symbol word set"


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

text\<open>In the following, we will also refer to the type of symbols (\<open>'symbol\<close> here)
  with the short form \<open>'s\<close>, and in locales with the generic \<open>'a\<close>%
  \<^footnote>\<open>When extending Isabelle locales, all type variables get replaced by generic ones (\<open>'a, 'b, 'c, ...\<close>)\<close>.\<close>


subsubsection\<open>Tape Head Movement\<close>

text\<open>We define TM tape head moves as either shifting the TM head one cell (left \<open>L\<close>, right \<open>R\<close>),
  or doing nothing (\<open>N\<close>).
  \<open>N\<close> seems redundant, since for single-tape TMs it can be simulated by moving the head back-and-forth
  or just leaving out any step that performs \<open>N\<close> (integrate into the preceding step).
  However, for multi-tape TMs, these simple replacements do not work.

  \<^emph>\<open>Moving the TM head\<close> is equivalent to shifting the entire tape under the head.
  This is how we implement the head movement.\<close>

datatype head_move = Shift_Left | Shift_Right | No_Shift

abbreviation (in TM_abbrevs) "L \<equiv> Shift_Left"
abbreviation (in TM_abbrevs) "R \<equiv> Shift_Right"
abbreviation (in TM_abbrevs) "N \<equiv> No_Shift"

(* consider introducing a type of actions:
 * type_synonym (in TM_abbrevs) ('s) action = "'s tp_symbol \<times> head_move" *)

subsection\<open>Turing Machines\<close>

text\<open>We model a (deterministic \<open>k\<close>-tape) TM over the type \<^typ>\<open>'q\<close> of states
  and the finite type \<^typ>\<open>'s\<close> of symbols, as a tuple of:\<close>

(* the inclusion of accepting states at this point seems somewhat arbitrary.
 * consider applying the "labelling" pattern used by @{cite forsterCoqTM2020},
 * as this would allow more advanced extensions, such as oracles as well *)

record ('q, 's::finite) TM_record =
  tape_count :: nat \<comment> \<open>\<open>k\<close>, the number of tapes\<close>
  states :: "'q set" \<comment> \<open>\<open>Q\<close>, the set of states\<close>
  initial_state  :: 'q \<comment> \<open>\<open>q\<^sub>0 \<in> Q\<close>, the initial state; computation will start on \<open>k\<close> blank tapes in this state\<close>
  final_states :: "'q set" \<comment> \<open>\<open>F \<subseteq> Q\<close>, the set of final states; if a TM is in a final state,
    its computation is considered finished (the TM has halted) and no further steps will be executed\<close>
  accepting_states :: "'q set" \<comment> \<open>\<open>F\<^sup>+ \<subseteq> F\<close>, the set of accepting states; if a TM halts in an accepting state,
    it is considered to have accepted the input\<close>

  next_state :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> 'q" \<comment> \<open>Maps the current state and vector of read symbols to the next state.\<close>
  next_write :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> nat \<Rightarrow> 's tp_symbol" \<comment> \<open>Maps the current state, read symbols and tape index
    to the symbol to write before transitioning to the next state.\<close>
  next_move  :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> nat \<Rightarrow> head_move" \<comment> \<open>Maps the current state, read symbols and tape index
    to the head movement to perform before transitionin to the next state.\<close>

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


subsubsection\<open>A Type of Turing Machines\<close>

text\<open>To use TMs conveniently, we setup a type and a locale as follows:

  \<^item> We have defined the structure of TMs as a record.
  \<^item> We define our validity predicate over \<open>TM_record\<close> as a locale, as this allows more convenient access to the axioms.
  \<^item> From the predicate, a type of (valid) TMs is defined.
  \<^item> Using the type, we set up definitions and lemmas concerning TMs within a locale.
    The locale allows convenient access to the internals of TMs.

  A simpler form of this pattern has been used to define the type of filters (\<^typ>\<open>'a filter\<close>).\<close>

locale is_valid_TM =
  fixes M :: "('q, 's::finite) TM_record" (structure)
  assumes at_least_one_tape: "1 \<le> tape_count M" (* TODO motivate this assm. "why is this necessary?" edit: initial_config would have to be defined differently *)
    and state_axioms: "finite (states M)" "initial_state M \<in> states M"
      "final_states M \<subseteq> states M" "accepting_states M \<subseteq> final_states M"
    and next_state_valid: "\<And>q hds. q \<in> states M \<Longrightarrow> next_state M q hds \<in> states M"

text\<open>To define a type, we must prove that it is inhabited (there exist elements that have this type).
  For this we define the trivial ``rejecting TM'', and prove it to be valid.\<close>

definition "rejecting_TM_rec a \<equiv> \<lparr>
  tape_count = 1,
  states = {a}, initial_state = a, final_states = {a}, accepting_states = {},
  next_state = (\<lambda>q hds. a), next_write = (\<lambda>q hds i. blank_symbol), next_move = (\<lambda>q hds i. No_Shift)
\<rparr>"

lemma rejecting_TM_valid: "is_valid_TM (rejecting_TM_rec a)"
  by (unfold_locales, unfold rejecting_TM_rec_def TM_record.simps) blast+

text\<open>The type \<open>TM\<close> is then defined as the set of valid \<open>TM_record\<close>s.\<close>
(* TODO elaborate on the implications of this *)

typedef ('q, 's::finite) TM = "{M :: ('q, 's) TM_record. is_valid_TM M}"
  using rejecting_TM_valid by fast

locale TM = TM_abbrevs +
  (* TODO find out what `(structure)` actually does. according to isar-ref.pdf,
   *      it allows the element to "be referenced implicitly in this context",
   *      but i have not yet seen any difference *)
  fixes M :: "('q, 's::finite) TM"
begin

abbreviation "M_rec \<equiv> Rep_TM M"

text\<open>Note: The following definitions ``overwrite'' the \<open>TM_record\<close> field names (such as \<^const>\<open>TM_record.states\<close>).
  This is not detrimental as in \<^locale>\<open>TM\<close> contexts these shortcuts are more convenient.
  One mildly annoying consequence is, however, that when defining a TM using the record constructor
  inside \<^locale>\<open>TM\<close> contexts, \<^const>\<open>TM_record.tape_count\<close> must be specified explicitly with its full name. (see below for an example)
  Interestingly, this only applies to the first field (\<^const>\<open>TM_record.tape_count\<close>) and not any of the other ones.\<close>

definition tape_count where "tape_count \<equiv> TM_record.tape_count M_rec"
definition states where "states \<equiv> TM_record.states M_rec"
definition initial_state where "initial_state \<equiv> TM_record.initial_state M_rec"
definition final_states where "final_states \<equiv> TM_record.final_states M_rec"
definition accepting_states ("F\<^sup>+") where "F\<^sup>+ \<equiv> TM_record.accepting_states M_rec"
definition rejecting_states ("F\<^sup>-") where "F\<^sup>- \<equiv> final_states - accepting_states"
definition next_state where "next_state \<equiv> TM_record.next_state M_rec"
definition next_write where "next_write \<equiv> TM_record.next_write M_rec"
definition next_move  where "next_move  \<equiv> TM_record.next_move  M_rec"

lemmas TM_fields_defs = tape_count_def states_def initial_state_def final_states_def
  accepting_states_def rejecting_states_def next_state_def next_write_def next_move_def

text\<open>The following abbreviations are not modelled as notation,
  as notation is not transferred when interpreting locales (see below).\<close>

abbreviation "k \<equiv> tape_count"
abbreviation "Q \<equiv> states"
abbreviation "q\<^sub>0 \<equiv> initial_state"
abbreviation "F \<equiv> final_states"
abbreviation "F\<^sub>A \<equiv> accepting_states"
abbreviation "F\<^sub>R \<equiv> rejecting_states"
abbreviation "\<delta>\<^sub>q \<equiv> next_state"
abbreviation "\<delta>\<^sub>w \<equiv> next_write"
abbreviation "\<delta>\<^sub>m \<equiv> next_move"


text\<open>We provide the following shortcuts for ``unpacking'' the transition function.
  \<open>hds\<close> refers to the symbols currently under the TM heads.\<close>

(* this is currently unused, and only included for demonstration *)
definition transition :: "'q \<Rightarrow> 's tp_symbol list \<Rightarrow> 'q \<times> ('s tp_symbol \<times> head_move) list"
  where "transition q hds = (\<delta>\<^sub>q q hds, map (\<lambda>i. (\<delta>\<^sub>w q hds i, \<delta>\<^sub>m q hds i)) [0..<k])"
abbreviation "\<delta> \<equiv> transition"

abbreviation "next_writes q hds \<equiv> map (\<delta>\<^sub>w q hds) [0..<k]"
abbreviation "next_moves q hds \<equiv> map (\<delta>\<^sub>m q hds) [0..<k]"
definition [simp]: "next_actions q hds \<equiv> zip (next_writes q hds) (next_moves q hds)"
abbreviation "\<delta>\<^sub>a \<equiv> next_actions"

lemma next_actions_altdef: "\<delta>\<^sub>a q hds = map (\<lambda>i. (\<delta>\<^sub>w q hds i, \<delta>\<^sub>m q hds i)) [0..<k]"
  unfolding next_actions_def zip_map_map map2_same ..


(* TODO consider removing [simp] here, as it would only be useful for low-level stuff *)
lemma M_rec[simp]: "M_rec = \<lparr> TM_record.tape_count = k, \<comment> \<open>as \<^const>\<open>TM.tape_count\<close> overwrites \<^const>\<open>TM_record.tape_count\<close>
        in \<^locale>\<open>TM\<close> contexts, it must be specified explicitly here.\<close>
    states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sup>+,
    next_state = \<delta>\<^sub>q, next_write = \<delta>\<^sub>w, next_move  = \<delta>\<^sub>m \<rparr>"
    unfolding TM_fields_defs by simp


subsubsection\<open>Properties\<close>

sublocale is_valid_TM M_rec using Rep_TM .. \<comment> \<open>The axioms of \<^locale>\<open>is_valid_TM\<close> hold by definition.\<close>

lemmas at_least_one_tape = at_least_one_tape[folded TM_fields_defs]
lemmas state_axioms = state_axioms[folded TM_fields_defs]
lemmas next_state_valid = next_state_valid[folded TM_fields_defs]
lemmas TM_axioms[intro, simp] = at_least_one_tape state_axioms next_state_valid

lemma next_actions_length[simp]: "length (next_actions q hds) = k" by simp

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


text\<open>The following code showcases the usage of TM concepts in this draft:\<close>

notepad
begin
  fix M M\<^sub>1 :: "('q, 's::finite) TM"

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
  Our definition of tapes allows no completely empty tape (containing zero symbols),
  as the \<^const>\<open>head\<close> symbol is always set.
  However, this makes sense concerning space-complexity,
  as a TM (depending on the exact definition) always reads at least one cell
  (and thus matches the requirement for space-complexity-functions to be at least \<open>1\<close> from @{cite hopcroftAutomata1979}).

  The use of datatype (as compared to record, for instance) grants the predefined
  \<^const>\<open>map_tape\<close> and \<^const>\<open>set_tape\<close>, including useful lemmas.\<close>

lemma tape_map_ident0[simp]: "map_tape (\<lambda>x. x) = (\<lambda>x. x)" by (rule ext) (rule tape.map_ident)

abbreviation empty_tape where "empty_tape \<equiv> Tape [] blank_symbol []"

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

corollary set_tape_simps[simp]:
  "set_tape \<langle>l|h|r\<rangle> = \<Union> (set_option ` (set l \<union> {h} \<union> set r))"
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
  (tapes: "'s tape list") \<comment> \<open>current contents of the tapes\<close>

text\<open>Combined with the \<^typ>\<open>('q, 's) TM\<close> definition, it completely describes a TM at any time during its execution.\<close>

type_synonym (in TM_abbrevs) ('q, 's) conf = "('q, 's) TM_config"
abbreviation (in TM_abbrevs) "conf \<equiv> TM_config"
abbreviation (in TM_abbrevs) "map_conf \<equiv> map_TM_config"
abbreviation (in TM_abbrevs) "map_conf_state \<equiv> \<lambda>fq. map_conf fq (\<lambda>s. s)"
abbreviation (in TM_abbrevs) "map_conf_tapes \<equiv> map_conf (\<lambda>q. q)"

declare TM_config.map_sel[simp]

abbreviation heads :: "('q, 's) TM_config \<Rightarrow> 's tp_symbol list" \<comment> \<open>The vector of symbols currently under the TM-heads\<close>
  where "heads c \<equiv> map head (tapes c)"

lemma map_head_tapes[simp]: "map head (map (map_tape f) tps) = map (map_option f) (map head tps)"
  unfolding map_map comp_def tape.map_sel ..

lemmas TM_config_eq = TM_config.expand[OF conjI] (* sadly, \<open>datatype\<close> does not provide this directly (cf. \<open>some_record.equality\<close> defined by \<open>record\<close> *)


context TM
begin

text\<open>A vector \<open>hds\<close> of symbols currently under the TM-heads,
  is considered a well-formed state w.r.t. a TM \<open>M\<close>,
  iff the number of elements of \<open>hds\<close> matches the number of tapes of \<open>M\<close>.\<close>

definition wf_state :: "'s tp_symbol list \<Rightarrow> bool" (* this is currently unused due to the mitigations put in place with next_actions *)
  where [simp]: "wf_state hds \<equiv> length hds = k"

text\<open>A \<^typ>\<open>('q, 's) TM_config\<close> \<open>c\<close> is considered well-formed w.r.t. a TM \<open>M\<close>,
  iff the number of \<^const>\<open>tapes\<close> of \<open>c\<close> matches the number of tapes of \<open>M\<close>.\<close>

definition wf_config :: "('q, 's) TM_config \<Rightarrow> bool"
  where [simp]: "wf_config c \<equiv> state c \<in> Q \<and> length (tapes c) = k"

(* TODO consider marking the intro as [simp] as well *)
mk_ide wf_config_def |intro wf_configI[intro]| |elim wf_configE[elim]| |dest wf_configD[dest]|


abbreviation is_final :: "('q, 's) TM_config \<Rightarrow> bool" where
  "is_final c \<equiv> state c \<in> F"

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


subsection\<open>TM Execution\<close>

subsubsection\<open>Actions\<close>

context TM_abbrevs
begin

text\<open>To execute a TM tape \<^typ>\<open>head_move\<close>, we shift the entire tape by one element.
  If the tape head is at the ``end'' of the defined tape, we insert \<^const>\<open>blank_symbol\<close>s,
  as the tape is considered infinite in both directions.\<close>

(* TODO split into shiftL and shiftR (maybe use symmetry) *)
fun tape_shift :: "head_move \<Rightarrow> 's tape \<Rightarrow> 's tape" where
  "tape_shift L     \<langle>|h|rs\<rangle>   =     \<langle>|Bk|h#rs\<rangle>"
| "tape_shift L \<langle>l#ls|h|rs\<rangle>   =   \<langle>ls|l |h#rs\<rangle>"
| "tape_shift R   \<langle>ls|h|\<rangle>     = \<langle>h#ls|Bk|\<rangle>"
| "tape_shift R   \<langle>ls|h|r#rs\<rangle> = \<langle>h#ls|r |rs\<rangle>"
| "tape_shift N tp = tp"

lemma tape_shift_set: "set_tape (tape_shift m tp) = set_tape tp" (* TODO consider removing *)
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


text\<open>Write a symbol to the current position of the TM tape head.\<close>

definition tape_write :: "'s tp_symbol \<Rightarrow> 's tape \<Rightarrow> 's tape"
  where "tape_write s tp = \<langle>left tp|s|right tp\<rangle>"

corollary tape_write_simps[simp]: "tape_write s \<langle>l|h|r\<rangle> = \<langle>l|s|r\<rangle>" unfolding tape_write_def by simp
corollary tape_write_id[simp]: "tape_write (head tp) tp = tp" by (induction tp) simp

lemma tape_write_map[simp]:
  "tape_write (map_option f s) (map_tape f tp) = map_tape f (tape_write s tp)"
  by (induction tp) simp


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

end \<comment> \<open>\<^locale>\<open>TM_abbrevs\<close>\<close>


subsubsection\<open>Steps\<close>

context TM
begin

text\<open>If the current state is not final,
  apply the action determined by \<^const>\<open>\<delta>\<close> for the current configuration.
  Otherwise, do not execute any action.\<close>

definition step_not_final :: "('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config"
  where "step_not_final c = (let q=state c; hds=heads c in conf
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
proof (rule nth_equalityI, unfold length_map length_zip next_actions_length l l' min.idem)
  fix i assume "i < k"
  then have [simp]: "[0..<k] ! i = i" by simp

  from \<open>i < k\<close> have "map2 tape_action (\<delta>\<^sub>a q hds) tps ! i = tape_action (\<delta>\<^sub>a q hds ! i) (tps ! i)"
    by (intro nth_map2) (auto simp add: l)
  also have "... = tape_action (\<delta>\<^sub>w q hds i, \<delta>\<^sub>m q hds i) (tps ! i)"
    unfolding next_actions_altdef using \<open>i < k\<close> by (subst nth_map) auto
  also from assms(3) and \<open>i < k\<close> have "... = tps' ! i" .
  finally show "map2 tape_action (\<delta>\<^sub>a q hds) tps ! i = tps' ! i" .
qed (rule refl)


definition step :: "('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config"
  where "step c = (if state c \<in> F then c else step_not_final c)"

abbreviation "steps n \<equiv> step ^^ n"

corollary step_simps[intro, simp]:
  shows step_final: "is_final c \<Longrightarrow> step c = c"
    and step_not_final: "\<not> is_final c \<Longrightarrow> step c = step_not_final c"
  unfolding step_def by auto


paragraph\<open>Final Steps\<close>

lemma final_steps[simp, intro]: "is_final c \<Longrightarrow> steps n c = c"
  by (rule funpow_fixpoint) (rule step_final)

corollary final_step_final[intro]: "is_final c \<Longrightarrow> is_final (step c)" by simp
corollary final_steps_final[intro]: "is_final c \<Longrightarrow> is_final (steps n c)" by simp

lemma final_le_steps:
  assumes "is_final (steps n c)"
    and "n \<le> m"
  shows "steps m c = steps n c"
proof -
  from \<open>n\<le>m\<close> obtain x where "m = x + n" unfolding le_iff_add by force
  have "(step^^m) c = (step^^x) ((step^^n) c)" unfolding \<open>m = x + n\<close> funpow_add by simp
  also have "... = (step^^n) c" using \<open>is_final (steps n c)\<close> by blast
  finally show "steps m c = steps n c" .
qed

corollary final_mono[elim]:
  assumes "is_final (steps n c)"
    and "n \<le> m"
  shows "is_final (steps m c)"
  unfolding final_le_steps[OF assms] by (fact \<open>is_final (steps n c)\<close>)

corollary final_mono': "mono (\<lambda>n. is_final (steps n c))"
  using final_mono by (intro monoI le_boolI)

lemma final_steps_rev:
  assumes "is_final (steps a c)"
    and "is_final (steps b c)"
  shows "steps a c = steps b c"
proof (cases a b rule: le_cases)
  case le with assms show ?thesis by (intro final_le_steps[symmetric]) next
  case ge with assms show ?thesis by (intro final_le_steps)
qed

lemma Least_final_step[intro, simp]:
  assumes "is_final (steps n c)"
  shows "steps (LEAST n. is_final (steps n c)) c = steps n c"
    (is "steps ?n' c = steps n c")
proof -
  from assms have "is_final (steps ?n' c)" by (rule LeastI)
  then show ?thesis using assms by (rule final_steps_rev)
qed


paragraph\<open>Well-Formed Steps\<close>

lemma step_nf_l_tps: "length (tapes c) = k \<Longrightarrow> length (tapes (step_not_final c)) = k" by simp
lemma step_nf_valid_state: "state c \<in> Q \<Longrightarrow> state (step_not_final c) \<in> Q" by simp
lemma wf_step_not_final[intro]: "wf_config c \<Longrightarrow> wf_config (step_not_final c)"
  using step_nf_l_tps step_nf_valid_state by blast

lemma step_l_tps: "length (tapes c) = k \<Longrightarrow> length (tapes (step c)) = k" by (cases "is_final c") auto
lemma step_valid_state: "state c \<in> Q \<Longrightarrow> state (step c) \<in> Q" by (cases "is_final c") auto
lemma wf_step[intro]: "wf_config c \<Longrightarrow> wf_config (step c)"
  using step_l_tps step_valid_state by blast

lemma steps_l_tps: "length (tapes c) = k \<Longrightarrow> length (tapes (steps n c)) = k" using step_l_tps by (elim funpow_induct)
lemma steps_valid_state: "state c \<in> Q \<Longrightarrow> state (steps n c) \<in> Q" using step_valid_state by (elim funpow_induct)
lemma wf_steps[intro]: "wf_config c \<Longrightarrow> wf_config (steps n c)" using wf_step by (elim funpow_induct)

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


subsection\<open>TM Modifications\<close>

subsubsection\<open>Reordering Tapes\<close>

(* TODO document this section *)

definition reorder :: "(nat option list) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "reorder is xs ys = map2 (\<lambda>i x. case is ! i of None \<Rightarrow> x | Some i' \<Rightarrow> nth_or i' x ys) [0..<length xs] xs"

value "reorder [Some 0, Some 2, Some 1, None] [w,x,y,z] [a,b,c]"

lemma reorder_length[simp]: "length (reorder is xs ys) = length xs" unfolding reorder_def by simp

lemma reorder_Nil[simp]: "reorder is xs [] = xs"
  unfolding reorder_def nth_or_Nil case_option_same prod.snd_def[symmetric] by simp

lemma reorder_nth[simp]:
  assumes "i < length xs"
  shows "reorder is xs ys ! i = (case is ! i of None \<Rightarrow> xs ! i | Some i' \<Rightarrow> nth_or i' (xs ! i) ys)"
  using assms unfolding reorder_def by (subst nth_map2) auto

lemma reorder_map[simp]: "map f (reorder is xs ys) = reorder is (map f xs) (map f ys)"
proof -
  let ?m = "\<lambda>d i x. case is ! i of None \<Rightarrow> d x | Some i' \<Rightarrow> nth_or i' (d x) (map f ys)"
  let ?m' = "\<lambda>d (i, x). ?m d i x" and ?id = "\<lambda>x. x"
  have "map f (reorder is xs ys) =
    map (\<lambda>(i, x). f (case is ! i of None \<Rightarrow> x | Some i' \<Rightarrow> nth_or i' x ys)) (zip [0..<length xs] xs)"
    unfolding reorder_def map_map comp_def by force
  also have "... = map2 (?m f) [0..<length xs] xs" unfolding option.case_distrib nth_or_map ..
  also have "... = map ((?m' ?id) \<circ> (\<lambda>(i, x). (i, f x))) (zip [0..<length xs] xs)" by fastforce
  also have "... = map (?m' ?id) (map (\<lambda>(i, x). (i, f x)) (zip [0..<length xs] xs))" by force
  also have "... = map2 (?m ?id) [0..<length xs] (map f xs)"
    unfolding zip_map_map[symmetric] list.map_ident ..
  also have "... = reorder is (map f xs) (map f ys)" unfolding reorder_def by simp
  finally show ?thesis .
qed


(* TODO are both xs and ys needed here? in practice they seem always be identical *)
definition reorder_inv :: "(nat option list) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "reorder_inv is ys = map
    (\<lambda>i. ys ! (LEAST i'. i'<length is \<and> is ! i' = Some i))
    [0..<if set is \<subseteq> {None} then 0 else Suc (Max (Option.these (set is)))]"


lemma card_these_helper: "card (Option.these (set xs)) \<le> length xs"
proof -
  have "card (Option.these (set xs)) \<le> card (set xs)" by (rule card_these) blast
  also have "... \<le> length xs" by (rule card_length)
  finally show ?thesis .
qed

lemma reorder_inv:
  assumes [simp]: "length xs = length is"
    and items_match: "Option.these (set is) = {0..<length ys}"
  shows "reorder_inv is (reorder is xs ys) = ys"
proof -
  define zs where "zs \<equiv> reorder is xs ys"
  have lz: "length zs = length xs" unfolding zs_def reorder_length ..

  have *: "(if set is \<subseteq> {None} then 0 else Suc (Max (Option.these (set is)))) = length ys"
  proof (rule ifI)
    assume "set is \<subseteq> {None}"
    then have "Option.these (set is) = {}" unfolding these_empty_eq subset_singleton_iff .
    then have "{0..<length ys} = {}" unfolding items_match .
    then show "0 = length ys" by simp
  next
    assume "\<not> set is \<subseteq> {None}"
    then have "Option.these (set is) \<noteq> {}" unfolding these_empty_eq subset_singleton_iff .
    then have "0 < length ys" unfolding items_match by simp
    then show "Suc (Max (Option.these (set is))) = length ys"
      unfolding items_match Max_atLeastLessThan_nat[OF \<open>length ys > 0\<close>] by simp
  qed

  have "length ys = card (Option.these (set is))" unfolding items_match by simp
  also have "... \<le> length is" by (rule card_these_helper)
  finally have ls: "length is \<ge> length ys" .

  have "reorder_inv is (reorder is xs ys) = map ((!) ys) [0..<length ys]"
    unfolding reorder_inv_def zs_def[symmetric] lz *
  proof (intro list.map_cong0)
    fix n assume "n \<in> set [0..<length ys]"
    then have [simp]: "n < length ys" by simp
    then have *: "[0..<length ys] ! n = n" by simp

    define i where "i = (LEAST i. i < length is \<and> is ! i = Some n)"

    from \<open>n < length ys\<close> have "n \<in> Option.these (set is)" unfolding items_match by simp
    then have "Some n \<in> set is" unfolding these_altdef by force
    then have ex_i[simp]: "\<exists>i. i < length is \<and> is ! i = Some n" unfolding in_set_conv_nth .

    then have "i < length is \<and> is ! i = Some n" unfolding i_def by (rule LeastI_ex)
    then have [simp]: "i < length is" and [simp]: "is ! i = Some n" by blast+
    then have [simp]: "[0..<length is] ! i = i" by simp

    show "zs ! (LEAST i'. i' < length is \<and> is ! i' = Some n) = ys ! n"
      unfolding i_def[symmetric] zs_def reorder_def by simp
  qed
  then show ?thesis unfolding map_nth .
qed

definition reorder_config :: "(nat option list) \<Rightarrow> 's tape list \<Rightarrow> ('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config"
  where "reorder_config is tps c = TM_config (state c) (reorder is tps (tapes c))"

lemma reorder_config_length[simp]: "length (tapes (reorder_config p tps c)) = length tps"
  unfolding reorder_config_def by simp

lemma reorder_config_simps[simp]:
  shows reorder_config_state: "state (reorder_config is tps c) = state c"
    and reorder_config_tapes: "tapes (reorder_config is tps c) = reorder is tps (tapes c)"
  unfolding reorder_config_def by simp_all


locale TM_reorder_tapes =
  fixes M :: "('q, 's::finite) TM"
    and "is" :: "nat option list"
  assumes items_match: "Option.these (set is) = {0..<TM.tape_count M}"
begin
sublocale TM .

abbreviation "k' \<equiv> length is"

lemma k_k': "k \<le> k'"
proof -
  have "k = card {0..<k}" by simp
  also have "... = card (Option.these (set is))" unfolding items_match ..
  also have "... \<le> card (set is)" by (rule card_these) blast
  also have "... \<le> k'" by (rule card_length)
  finally show "k \<le> k'" .
qed

definition reorder_tapes_rec :: "('q, 's) TM_record"
  where "reorder_tapes_rec \<equiv>
    let h = reorder_inv is in
    M_rec \<lparr>
      tape_count := k',
      next_state := \<lambda>q hds. \<delta>\<^sub>q q (h hds),
      next_write := \<lambda>q hds i. case is ! i of Some i \<Rightarrow> (\<delta>\<^sub>w q (h hds) i) | None \<Rightarrow> hds ! i,
      next_move  := \<lambda>q hds i. case is ! i of Some i \<Rightarrow> (\<delta>\<^sub>m q (h hds) i) | None \<Rightarrow> No_Shift
    \<rparr>"

lemma reorder_tapes_rec_simps: "reorder_tapes_rec = \<lparr>
  TM_record.tape_count = k',
  states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sup>+,
  next_state = \<lambda>q hds. \<delta>\<^sub>q q (reorder_inv is hds),
  next_write = \<lambda>q hds i. case is ! i of Some i \<Rightarrow> (\<delta>\<^sub>w q (reorder_inv is hds) i) | None \<Rightarrow> hds ! i,
  next_move  = \<lambda>q hds i. case is ! i of Some i \<Rightarrow> (\<delta>\<^sub>m q (reorder_inv is hds) i) | None \<Rightarrow> No_Shift
\<rparr>" unfolding reorder_tapes_rec_def Let_def by simp

definition "M' \<equiv> Abs_TM reorder_tapes_rec"

lemma M'_valid: "is_valid_TM reorder_tapes_rec"
  unfolding reorder_tapes_rec_simps
proof (unfold_locales, unfold TM_record.simps)
  from at_least_one_tape and k_k' show "1 \<le> k'" by simp
qed (fact TM_axioms)+

sublocale M': TM M' .

lemma M'_rec: "M'.M_rec = reorder_tapes_rec" using Abs_TM_inverse M'_valid by (auto simp add: M'_def)
lemmas M'_fields = M'.TM_fields_defs[unfolded M'_rec reorder_tapes_rec_simps TM_record.simps]
lemmas [simp] = M'_fields(1-6)

lemma reorder_step:
  assumes "wf_config c"
    and l_tps': "length (tapes c') = k'"
  shows "M'.step (reorder_config is (tapes c') c) = reorder_config is (tapes c') (step c)"
    (is "M'.step (?rc c) = ?rc (step c)")
proof (cases "is_final c")
  assume "is_final c"
  then have "M'.is_final (?rc c)" by simp
  then have "M'.step (?rc c) = (?rc c)" by fast
  also from \<open>is_final c\<close> have "... = ?rc (step c)" by simp
  finally show ?thesis .
next
  let ?c' = "?rc c"
  let ?q = "state c" and ?q' = "state ?c'"
  let ?tps = "tapes c" and ?hds = "heads c"

  let ?r = "reorder is" let ?rt = "?r (tapes c')"
  let ?hds' = "?r (heads c') ?hds" and ?tps' = "?rt ?tps"

  from \<open>wf_config c\<close> have l_tps: "length (tapes c) = k" by simp
  then have l_hds: "length (heads c) = k" by simp
  from l_tps' have l_hds': "length (heads c') = k'" by simp

  moreover have "Option.these (set is) = {0..<length ?hds}" unfolding l_hds items_match ..
  ultimately have r_inv_hds[simp]: "reorder_inv is (reorder is (heads c') ?hds) = ?hds" by (rule reorder_inv)

  assume "\<not> is_final c"
  then have "M'.step ?c' = M'.step_not_final ?c'" by simp
  also have "... = ?rc (step_not_final c)"
  proof (intro TM_config.expand conjI)
    have "state (M'.step_not_final ?c') = M'.\<delta>\<^sub>q ?q ?hds'"
      unfolding M'.step_not_final_def by (simp add: Let_def)
    also have "... = \<delta>\<^sub>q ?q ?hds" unfolding M'_fields by simp
    also have "... = state (?rc (step_not_final c))" by simp
    finally show "state (M'.step_not_final ?c') = state (?rc (step_not_final c))" .

    from k_k' have min_k_k': "min k M'.k = k" by simp
    have lr: "length (reorder is (tapes c') x) = M'.k" for x by (simp add: l_tps')

    have "tapes (M'.step_not_final ?c') = map2 tape_action (M'.\<delta>\<^sub>a ?q ?hds') ?tps'"
      unfolding M'.step_not_final_def by (simp add: Let_def)
    also have "... = ?r (tapes c') (map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps)"
    proof (rule M'.step_not_final_eqI)
      fix i assume "i < M'.k"
      then have [simp]: "i < k'" by simp

      show "tape_action (M'.\<delta>\<^sub>w ?q ?hds' i, M'.\<delta>\<^sub>m ?q ?hds' i) (?tps' ! i) =
        ?rt (map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps) ! i"
      proof (induction "is ! i")
        case None
        then have [simp]: "is ! i = None" ..
        from \<open>i < k'\<close> have "reorder is xs ys ! i = xs ! i" if "length xs = k'" for xs ys :: "'x list"
          using that by simp
        note * = this[OF l_tps'] this[OF l_hds']
        from \<open>i < k'\<close> have [simp]: "map head (tapes c') ! i = head (tapes c' ! i)"
          by (intro nth_map) (unfold l_tps')
        show ?case unfolding M'_fields * by simp
      next
        case (Some i')
        then have [simp]: "is ! i = Some i'" ..

        from \<open>i < k'\<close> have "i \<in> {0..<k'}" by simp
        then have "Some i' \<in> set is" unfolding \<open>Some i' = is ! i\<close> using \<open>i < k'\<close> nth_mem by blast
        then have "i' \<in> {0..<k}" unfolding items_match[symmetric] in_these_eq .
        then have [simp]: "i' < k" by simp

        then have nth_i': "nth_or i' x xs = xs ! i'" if "length xs = k" for x :: 'x and xs
          unfolding nth_or_def \<open>length xs = k\<close> by (rule if_P)
        from \<open>i < k'\<close> have "i < length (tapes c')" unfolding l_tps' .
        then have r_nth_or: "reorder is (tapes c') tps ! i = nth_or i' (tapes c' ! i) tps" for tps
          by simp

        have \<delta>\<^sub>w': "M'.\<delta>\<^sub>w ?q ?hds' i = \<delta>\<^sub>w (state c) (heads c) i'"
         and \<delta>\<^sub>m': "M'.\<delta>\<^sub>m ?q ?hds' i = \<delta>\<^sub>m (state c) (heads c) i'"
          unfolding M'_fields by simp_all

        have "tape_action (M'.\<delta>\<^sub>w ?q ?hds' i, M'.\<delta>\<^sub>m ?q ?hds' i) (?tps' ! i) =
              tape_action (   \<delta>\<^sub>w ?q ?hds i',    \<delta>\<^sub>m ?q ?hds i') (?tps ! i')"
          unfolding \<delta>\<^sub>w' \<delta>\<^sub>m' unfolding r_nth_or nth_i'[OF l_tps] ..
        also have "... = tape_action (\<delta>\<^sub>a ?q ?hds ! i') (?tps ! i')" by simp
        also have "... = map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps ! i'" by (auto simp add: l_tps)
        also have "... = ?rt (map2 tape_action (\<delta>\<^sub>a ?q ?hds) ?tps) ! i"
          unfolding r_nth_or by (rule nth_i'[symmetric]) (simp add: l_tps)
        finally show ?case .
      qed
    qed (fact lr)+
    also have "... = tapes (?rc (step_not_final c))" by (simp add: Let_def)
    finally show "tapes (M'.step_not_final ?c') = tapes (?rc (step_not_final c))" .
  qed
  also from \<open>\<not> is_final c\<close> have "... = ?rc (step c)" by simp
  finally show ?thesis .
qed

corollary reorder_steps:
  fixes c c' :: "('q, 's) TM_config"
  assumes wfc: "wf_config c"
    and wfc': "length (tapes c') = k'"
  shows "M'.steps n (reorder_config is (tapes c') c) = reorder_config is (tapes c') (steps n c)"
    (is "M'.steps n (?rc c) = ?rc (steps n c)")
proof (induction n)
  case (Suc n)
  from \<open>wf_config c\<close> have wfcs: "wf_config (steps n c)" by blast
  show ?case unfolding funpow.simps comp_def Suc.IH reorder_step[OF wfcs wfc'] ..
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

end \<comment> \<open>\<^locale>\<open>TM_reorder_tapes\<close>\<close>


context TM
begin

definition reorder_tapes :: "nat option list \<Rightarrow> ('q, 's::finite) TM"
  where "reorder_tapes is \<equiv> TM_reorder_tapes.M' M is"

corollary reorder_tapes_steps:
  fixes c c' :: "('q, 's) TM_config"
  assumes "wf_config c"
    and "length (tapes c') = length is"
    and "Option.these (set is) = {0..<k}"
  shows "TM.steps (reorder_tapes is) n (reorder_config is (tapes c') c) = reorder_config is (tapes c') (steps n c)"
  unfolding reorder_tapes_def using assms
  by (intro TM_reorder_tapes.reorder_steps) (unfold_locales)


definition tape_offset :: "nat \<Rightarrow> nat \<Rightarrow> nat option list"
  where "tape_offset a b \<equiv> None\<up>a @ (map Some [0..<k]) @ None\<up>b"

lemma tape_offset_length[simp]: "length (tape_offset a b) = a + k + b"
  unfolding tape_offset_def by simp

lemma tape_offset_valid: "Option.these (set (tape_offset a b)) = {0..<k}"
proof -
  let ?o = "tape_offset a b"
  have [simp]: "set ?o = set (None \<up> a) \<union> Some ` {0..<k} \<union> set (None \<up> b)"
    unfolding tape_offset_def by force
  have [simp]: "Option.these (set (None \<up> i)) = {}" for i by (induction i) auto
  show "Option.these (set ?o) = {0..<k}" by simp
qed

theorem tape_offset_steps:
  fixes c c' :: "('q, 's) TM_config"
    and a b :: nat
  defines "is \<equiv> tape_offset a b"
  assumes "wf_config c"
    and "length (tapes c') = length is"
  shows "TM.steps (reorder_tapes is) n (reorder_config is (tapes c') c) = reorder_config is (tapes c') (steps n c)"
  using assms tape_offset_valid unfolding reorder_tapes_def is_def
  by (intro TM_reorder_tapes.reorder_steps) (unfold_locales)

end


subsubsection\<open>Change Alphabet\<close>

locale TM_map_alphabet =
  fixes M :: "('q, 's1::finite) TM"
    and f :: "'s1 \<Rightarrow> 's2::finite" \<comment> \<open>Specifying the inverse instead of defining it using \<^const>\<open>inv\<close>
          leaves no unspecified cases.\<close>
  assumes inj_f: "inj f"
begin
sublocale TM .

abbreviation f' where "f' \<equiv> map_option f"
definition f_inv ("f\<inverse>") where "f_inv \<equiv> inv f"
abbreviation f'_inv ("f''\<inverse>") where "f'_inv \<equiv> map_option f_inv"

lemma inv_f_f[simp]: "f_inv (f x) = x" "f_inv \<circ> f = (\<lambda>x. x)"
  unfolding comp_def f_inv_def using inj_f by simp_all
lemma inv_f'_f'[simp]: "f'_inv (f' x) = x" "f'_inv \<circ> f' = (\<lambda>x. x)"
  by (simp_all add: comp_def option.map_comp option.map_ident)
lemma map_f'_inv[simp]: "map f'_inv (map f' xs) = xs" by simp (* useless *)

lemma surj_f_inv: "surj f_inv" unfolding f_inv_def using inj_f by (rule inj_imp_surj_inv)


definition fc where "fc \<equiv> map_conf_tapes f"

lemma fc_simps[simp]:
  shows "state (fc c) = state c"
    and "tapes (fc c) = map (map_tape f) (tapes c)"
  unfolding fc_def TM_config.map_sel by (rule refl)+

definition map_alph_rec :: "('q, 's2) TM_record"
  where "map_alph_rec \<equiv> \<lparr>
    TM_record.tape_count = k,
    states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sup>+,
    next_state = \<lambda>q hds. if set hds \<subseteq> range f' then \<delta>\<^sub>q q (map f'_inv hds) else q,
    next_write = \<lambda>q hds i. if set hds \<subseteq> range f' then f' (\<delta>\<^sub>w q (map f'_inv hds) i) else hds ! i,
    next_move  = \<lambda>q hds i. if set hds \<subseteq> range f' then \<delta>\<^sub>m q (map f'_inv hds) i else N
  \<rparr>"

lemma M'_valid: "is_valid_TM map_alph_rec"
  unfolding map_alph_rec_def
proof (unfold_locales, unfold TM_record.simps)
  fix q hds assume "q \<in> Q"
  then show "(if set hds \<subseteq> range f' then \<delta>\<^sub>q q (map f'\<inverse> hds) else q) \<in> Q" by simp
qed (fact TM_axioms)+

definition "M' \<equiv> Abs_TM map_alph_rec"
sublocale M': TM M' .

lemma M'_rec: "M'.M_rec = map_alph_rec" using Abs_TM_inverse M'_valid by (auto simp add: M'_def)
lemmas M'_fields = M'.TM_fields_defs[unfolded M'_rec map_alph_rec_def TM_record.simps]
lemmas [simp] = M'_fields(1-6)

lemma map_step:
  assumes [simp]: "length (tapes c) = k"
  shows "M'.step (fc c) = fc (step c)"
proof (cases "is_final c") (* TODO extract this pattern as lemma *)
  assume "is_final c"
  then show ?thesis by simp
next
  let ?c' = "fc c"
  let ?q = "state c" and ?q' = "state ?c'"
  let ?tps = "tapes c" and ?hds = "heads c"

  let ?ft = "map (map_tape f)"
  let ?hds' = "map f' ?hds" and ?tps' = "?ft ?tps"

  assume "\<not> is_final c"
  then have "M'.step ?c' = M'.step_not_final ?c'" by simp
  also have "... = fc (step_not_final c)"
  proof (rule TM_config_eq)
    have set_hds'[intro]: "set ?hds' \<subseteq> range f'" by blast
    then show "state (M'.step_not_final ?c') = state (fc (step_not_final c))"
      unfolding fc_simps TM.step_not_final_simps M'_fields by (simp add: comp_def tape.map_sel)

    show "tapes (M'.step_not_final ?c') = tapes (fc (step_not_final c))"
      unfolding TM.step_not_final_simps
    proof (intro TM.step_not_final_eqI, unfold fc_simps map_head_tapes)
      fix i assume "i < M'.k"
      then have [simp]: "i < k" by simp

      then have **: "?tps' ! i = map_tape f (tapes c ! i)" by simp
      have *: "(if set ?hds' \<subseteq> range f' then a else b) = a" for a b :: 'x by (blast intro: if_P)

      have "tape_action (M'.\<delta>\<^sub>w ?q ?hds' i, M'.\<delta>\<^sub>m ?q ?hds' i) (?tps' ! i)
          = tape_action (f' (\<delta>\<^sub>w ?q ?hds i), \<delta>\<^sub>m ?q ?hds i) (?tps' ! i)"
        unfolding M'_fields * map_f'_inv ..
      also have "... = tape_action (f' (\<delta>\<^sub>w ?q ?hds i), \<delta>\<^sub>m ?q ?hds i) (map_tape f (?tps ! i))"
        by (subst nth_map) auto
      also have "... = map_tape f (tape_action (\<delta>\<^sub>w ?q ?hds i, \<delta>\<^sub>m ?q ?hds i) (?tps ! i))" by simp
      also have "... = ?ft (tapes (step_not_final c)) ! i" by simp
      finally show "tape_action (M'.\<delta>\<^sub>w ?q ?hds' i, M'.\<delta>\<^sub>m ?q ?hds' i) (?tps' ! i) =
         ?ft (tapes (step_not_final c)) ! i" .
    qed simp_all
  qed
  also from \<open>\<not> is_final c\<close> have "... = fc (step c)" by simp
  finally show ?thesis .
qed

corollary map_steps:
  assumes l_tps: "length (tapes c) = k"
  shows "M'.steps n (fc c) = fc (steps n c)"
  using assms
proof (induction n)
  case (Suc n)
  then have IH: "M'.steps n (fc c) = fc (steps n c)" by blast
  from \<open>length (tapes c) = k\<close> have l_tpss: "length (tapes (steps n c)) = k" by (rule steps_l_tps)

  show ?case unfolding funpow.simps comp_def IH map_step[OF l_tpss] ..
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

end \<comment> \<open>\<^locale>\<open>TM_map_alphabet\<close>\<close>

context TM
begin


definition map_alphabet :: "('s \<Rightarrow> 's2::finite) \<Rightarrow> ('q, 's2) TM"
  where "map_alphabet f \<equiv> TM_map_alphabet.M' M f"

theorem map_alphabet_steps:
  fixes f :: "'s \<Rightarrow> 's2::finite"
  assumes "length (tapes c) = k"
    and "inj f"
  shows "TM.steps (map_alphabet f) n (map_conf_tapes f c) = map_conf_tapes f (steps n c)"
proof -
  interpret TM_map_alphabet M f using \<open>inj f\<close> by (unfold_locales)
  from \<open>length (tapes c) = k\<close> have "M'.steps n (fc c) = fc (steps n c)" by (rule map_steps)
  then show ?thesis unfolding map_alphabet_def fc_def .
qed

end


subsubsection\<open>Simple Composition\<close>

locale simple_TM_comp = TM_abbrevs +
  fixes M1 :: "('q1, 's::finite) TM"
    and M2 :: "('q2, 's::finite) TM"
  assumes k: "TM.tape_count M1 = TM.tape_count M2"
begin
sublocale M1: TM M1 .
sublocale M2: TM M2 .

definition comp_rec :: "('q1 + 'q2, 's) TM_record"
  where "comp_rec \<equiv> \<lparr>
    TM_record.tape_count = M1.k,
    states = Inl ` M1.Q \<union> Inr ` M2.Q,
    initial_state = Inl M1.q\<^sub>0,
    final_states = Inr ` M2.F,
    accepting_states = Inr ` M2.F\<^sub>A,
    next_state = \<lambda>q hds. case q of Inl q1 \<Rightarrow> let q1' = M1.\<delta>\<^sub>q q1 hds in
                                             if q1' \<in> M1.F then Inr M2.q\<^sub>0 else Inl q1'
                                 | Inr q2 \<Rightarrow> Inr (M2.\<delta>\<^sub>q q2 hds),
    next_write = \<lambda>q hds i. case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>w q1 hds i | Inr q2 \<Rightarrow> M2.\<delta>\<^sub>w q2 hds i,
    next_move  = \<lambda>q hds i. case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>m q1 hds i | Inr q2 \<Rightarrow> M2.\<delta>\<^sub>m q2 hds i
  \<rparr>"

lemma M_valid: "is_valid_TM comp_rec" unfolding comp_rec_def
proof (unfold_locales, unfold TM.simps)
  fix q hds
  assume "q \<in> Inl ` M1.Q \<union> Inr ` M2.Q"
  then show "(case q of Inl q1 \<Rightarrow> let q1' = M1.\<delta>\<^sub>q q1 hds in if q1' \<in> M1.F then Inr M2.q\<^sub>0 else Inl q1'
        | Inr q2 \<Rightarrow> Inr (M2.\<delta>\<^sub>q q2 hds))
       \<in> Inl ` M1.Q \<union> Inr ` M2.Q" (is "(case q of Inl q1 \<Rightarrow> ?l q1 | Inr q2 \<Rightarrow> ?r q2) \<in> ?Q")
  proof (induction q)
    case (Inl q1)
    show ?case unfolding sum.case Let_def by (rule if_cases) (use Inl in blast)+
  next
    case (Inr q2)
    then show ?case unfolding sum.case by blast
  qed
qed (use M2.TM_axioms(4-5) in blast)+

definition "M \<equiv> Abs_TM comp_rec"

sublocale TM M .

lemma M_rec: "M_rec = comp_rec" unfolding M_def using M_valid by (intro Abs_TM_inverse CollectI)
lemmas M_fields = TM_fields_defs[unfolded M_rec comp_rec_def TM_record.simps Let_def]
lemmas [simp] = M_fields(1-6)

lemma next_state_simps[simp]:
  shows "M1.\<delta>\<^sub>q q1 hds \<in> M1.F \<Longrightarrow> \<delta>\<^sub>q (Inl q1) hds = Inr M2.q\<^sub>0"
    and "M1.\<delta>\<^sub>q q1 hds \<notin> M1.F \<Longrightarrow> \<delta>\<^sub>q (Inl q1) hds = Inl (M1.\<delta>\<^sub>q q1 hds)"
    and "\<delta>\<^sub>q (Inr q2) hds = Inr (M2.\<delta>\<^sub>q q2 hds)"
  unfolding M_fields by auto

definition cl :: "('q1, 's) TM_config \<Rightarrow> ('q1 + 'q2, 's) TM_config"
  where "cl \<equiv> map_conf_state Inl"
definition cl' :: "('q1 + 'q2, 's) TM_config \<Rightarrow> ('q1, 's) TM_config"
  where "cl' \<equiv> map_conf_state projl"

lemma cl_state[simp]: "state (cl c) = Inl (state c)" unfolding cl_def by simp
lemma cl'_tapes[simp]: "tapes (cl' c) = tapes c" unfolding cl'_def by simp

lemma cl'_cl[simp]: "cl' (cl c) = c" unfolding cl_def cl'_def TM_config.map_comp comp_def sum.sel TM_config.map_ident ..

lemma cl_cl'[simp]: "isl (state c) \<Longrightarrow> cl (cl' c) = c"
proof (induction c)
  case (TM_config q tps)
  then obtain q1 where q1: "q = Inl q1" by (induction q) auto
  show ?case unfolding cl_def cl'_def TM_config.map_comp comp_def q1
    unfolding TM_config.map sum.sel tape.map_ident by simp
qed

lemma comp_step1_not_final:
  assumes "isl (state c)" (* TODO there may be a more streamlined way to word this assumption *)
    and step_nf: "\<not> M1.is_final (M1.step (cl' c))"
  shows "step c = cl (M1.step (cl' c))"
proof -
  from step_nf have nf': "\<not> M1.is_final (cl' c)" by auto
  with \<open>isl (state c)\<close> have nf: "\<not> is_final c" by auto

  then have "step c = step_not_final c" by blast
  also have "... = cl (M1.step_not_final (cl' c))"
  proof (rule TM_config_eq)
    from \<open>isl (state c)\<close> obtain q1 where [simp]: "state c = Inl q1" unfolding isl_def ..
    then have [simp]: "state (cl' c) = q1" unfolding cl'_def by simp
    from step_nf have *: "M1.\<delta>\<^sub>q q1 (heads c) \<notin> M1.F" using nf' by simp

    show "state (step_not_final c) = state (cl (M1.step_not_final (cl' c)))" using * by simp
    show "tapes (step_not_final c) = tapes (cl (M1.step_not_final (cl' c)))"
      unfolding cl_def by (simp add: M_fields(8-9))
  qed
  also from nf' have "... = cl (M1.step (cl' c))" by simp
  finally show ?thesis .
qed

lemma comp_step1_next_final:
  assumes "isl (state c)"
    and nf': "\<not> M1.is_final (cl' c)"
    and step_final: "M1.is_final (M1.step (cl' c))"
  shows "step c = conf (Inr M2.q\<^sub>0) (tapes (M1.step (cl' c)))"
proof -
  from assms(1-2) have nf: "\<not> is_final c" by auto

  then have "step c = step_not_final c" by blast
  also have "... = conf (Inr M2.q\<^sub>0) (tapes (M1.step_not_final (cl' c)))"
  proof (rule TM_config_eq, unfold TM_config.sel)
    from \<open>isl (state c)\<close> obtain q1 where [simp]: "state c = Inl q1" unfolding isl_def ..
    then have [simp]: "state (cl' c) = q1" unfolding cl'_def by simp
    from step_final have *: "M1.\<delta>\<^sub>q q1 (heads c) \<in> M1.F" using nf' by simp

    show "state (step_not_final c) = Inr M2.q\<^sub>0" using * by simp
    show "tapes (step_not_final c) = tapes (M1.step_not_final (cl' c))" by (simp add: M_fields(8-9))
  qed
  also from nf' have "... = conf (Inr M2.q\<^sub>0) (tapes (M1.step (cl' c)))"
    by (subst M1.step_simps(2)) blast+
  finally show ?thesis .
qed

lemma comp_step2: "step (map_conf_state Inr c) = map_conf_state Inr (M2.step c)"
  (is "step (?cr c) = ?cr (M2.step c)")
proof (cases "M2.is_final c")
  assume nf: "\<not> M2.is_final c"
  then have "\<not> is_final (?cr c)" by force

  then have "step (?cr c) = step_not_final (?cr c)" by blast
  also have "... = ?cr (M2.step_not_final c)"
  proof (rule TM_config_eq)
    show "state (step_not_final (?cr c)) = state (?cr (M2.step_not_final c))" by simp
    show "tapes (step_not_final (?cr c)) = tapes (?cr (M2.step_not_final c))" by (simp add: k M_fields(8-9))
  qed
  also from nf have "... = ?cr (M2.step c)" by simp
  finally show ?thesis .
qed \<comment> \<open>case \<^term>\<open>M2.is_final c\<close> by\<close> simp


lemma comp_steps_final: (* TODO split into steps up to n1' (not final) and the rest *)
  fixes c_init1 n1 n2
  defines "c_fin1 \<equiv> M1.steps n1 c_init1"
  defines "c_init2 \<equiv> conf M2.q\<^sub>0 (tapes c_fin1)"
  defines "c_fin2 \<equiv> M2.steps n2 c_init2"
  assumes ci1_nf: "\<not> M1.is_final c_init1"
    and cf1: "M1.is_final c_fin1"
    and cf2: "M2.is_final c_fin2"
  shows "steps (n1+n2) (map_conf_state Inl c_init1) = map_conf_state Inr c_fin2"
    (is "steps ?n ?c0 = ?c_fin")
proof -
  let ?cl = "map_conf_state Inl" and ?cr = "map_conf_state Inr"
  let ?fs1 = "\<lambda>n. M1.is_final (M1.steps n c_init1)"

  from ci1_nf cf1 have "\<exists>n1'<n1. (\<forall>i\<le>n1'. \<not> ?fs1 i) \<and> ?fs1 (Suc n1')"
    unfolding c_fin1_def by (intro ex_least_nat_less) auto
  then obtain n1' where "n1' < n1" and nfs1: "\<And>i. i \<le> n1' \<Longrightarrow> \<not>?fs1 i" and "?fs1 (Suc n1')" by blast
  then have "\<not>?fs1 n1'" by blast

  have "0 \<le> n1'" by (rule le0)
  then have steps_n1': "steps n1' ?c0 = cl (M1.steps n1' c_init1)"
    and isl_n1': "isl (state (steps n1' ?c0))"
  proof (induction n1' rule: dec_induct)
    case base
    show "steps 0 ?c0 = cl (M1.steps 0 c_init1)" and "isl (state (steps 0 ?c0))"
      unfolding funpow_0 cl_def[symmetric] by auto
  next
    case (step n)
    have "steps (Suc n) ?c0 = step (steps n ?c0)" unfolding funpow.simps comp_def ..
    also have "... = step (cl (M1.steps n c_init1))" unfolding step.IH ..
    also have "... = cl (M1.step (cl' (cl (M1.steps n c_init1))))"
    proof (rule comp_step1_not_final)
      show "isl (state (cl (M1.steps n c_init1)))" by simp
      from \<open>n < n1'\<close> have "\<not>?fs1 (Suc n)" by (intro nfs1 Suc_leI)
      then show "\<not> M1.is_final (M1.step (cl' (cl (M1.steps n c_init1))))"
        unfolding cl'_cl funpow.simps comp_def .
    qed
    also have "... = cl (M1.steps (Suc n) c_init1)" by simp
    finally show *: "steps (Suc n) ?c0 = cl (M1.steps (Suc n) c_init1)" .

    show "isl (state (steps (Suc n) ?c0))" unfolding * by simp
  qed

  from \<open>?fs1 (Suc n1')\<close> and \<open>n1' < n1\<close> have c_fin1_alt: "c_fin1 = M1.steps (Suc n1') c_init1"
    unfolding c_fin1_def by (intro M1.final_le_steps Suc_leI)

  from isl_n1' have "steps (Suc n1') ?c0 = conf (Inr M2.q\<^sub>0) (tapes (M1.step (cl' (cl (M1.steps n1' c_init1)))))"
    using \<open>\<not>?fs1 n1'\<close> and \<open>?fs1 (Suc n1')\<close> unfolding funpow.simps comp_def steps_n1'
    by (intro comp_step1_next_final; (unfold cl'_cl)?) blast+ (* TODO Isar-ify this proof *)

  also have "... = conf (Inr M2.q\<^sub>0) (tapes c_fin1)" unfolding c_fin1_alt cl'_cl funpow.simps comp_def ..
  also have "... = ?cr c_init2" unfolding c_init2_def by simp
  finally have steps_Sn1': "steps (Suc n1') ?c0 = ?cr c_init2" .

  have "0 \<le> n2" by (rule le0)
  then have steps_n2: "steps n2 (?cr c_init2) = ?cr (M2.steps n2 c_init2)"
  proof (induction n2 rule: dec_induct)
    case (step n2)
    show ?case unfolding funpow.simps comp_def unfolding step.IH comp_step2 ..
  qed simp

  from cf2 have "is_final (steps (n2 + Suc n1') ?c0)"
    unfolding funpow_add comp_def steps_Sn1' steps_n2 c_fin2_def by simp
  moreover from \<open>n1' < n1\<close> have "n2 + Suc n1' \<le> ?n" by auto
  ultimately have "steps ?n ?c0 = steps (n2 + Suc n1') ?c0" by (rule final_le_steps)

  also have "... = steps n2 (?cr c_init2)" unfolding funpow_add comp_def steps_Sn1' ..
  also have "... = ?c_fin" unfolding c_fin2_def steps_n2 ..
  finally show ?thesis .
qed

end


definition TM_comp :: "('q1, 's::finite) TM \<Rightarrow> ('q2, 's) TM \<Rightarrow> ('q1 + 'q2, 's) TM"
  where "TM_comp M1 M2 \<equiv> simple_TM_comp.M M1 M2"

theorem TM_comp_steps_final:
  fixes M1 :: "('q1, 's::finite) TM" and M2 :: "('q2, 's) TM"
    and c_init1 :: "('q1, 's) TM_config"
    and n1 n2 :: nat
  assumes k: "TM.tape_count M1 = TM.tape_count M2"
  defines "c_fin1 \<equiv> TM.steps M1 n1 c_init1"
  assumes c_init2_def: "c_init2 \<equiv> TM_config (TM.q\<^sub>0 M2) (tapes c_fin1)" \<comment> \<open>Assumed, not defined, to reduce the term size of the overall lemma.\<close>
  defines "c_fin2 \<equiv> TM.steps M2 n2 c_init2"
  assumes ci1_nf: "\<not> TM.is_final M1 c_init1"
    and cf1: "TM.is_final M1 c_fin1"
    and cf2: "TM.is_final M2 c_fin2"
  shows "TM.steps (TM_comp M1 M2) (n1+n2) (map_TM_config Inl (\<lambda>x. x) c_init1) = map_TM_config Inr (\<lambda>x. x) c_fin2"
    (is "TM.steps ?M ?n ?c0 = ?c_fin")
  using k ci1_nf cf1 cf2
  unfolding c_fin1_def c_init2_def c_fin2_def TM_comp_def simple_TM_comp_def[symmetric]
  by (rule simple_TM_comp.comp_steps_final)


subsection\<open>Computation on TMs\<close>

context TM
begin

text\<open>We follow the convention that TMs read their input from the first tape
  and write their output to the last tape.\<close>
  (* TODO is this *the* standard convention? what about output on the first tape? *)


subsubsection\<open>Input\<close>

text\<open>TM execution begins with the head at the start of the input word.
  The remaining symbols of the word can be reached by shifting the tape head to the right.
  The end of the word is reached when the tape head first encounters \<^const>\<open>blank_symbol\<close>.\<close>

fun input_tape :: "'s word \<Rightarrow> 's tape" ("<_>\<^sub>t\<^sub>p") where
  "<[]>\<^sub>t\<^sub>p = \<langle>\<rangle>"
| "<x # xs>\<^sub>t\<^sub>p = \<langle>|Some x|map Some xs\<rangle>"

lemma input_tape_map: "map_tape f <w>\<^sub>t\<^sub>p = <map f w>\<^sub>t\<^sub>p" by (induction w) auto

lemma input_tape_left[simp]: "left <w>\<^sub>t\<^sub>p = []" by (induction w) auto
lemma input_tape_right: "w \<noteq> [] \<longleftrightarrow> head <w>\<^sub>t\<^sub>p # right <w>\<^sub>t\<^sub>p = map Some w" by (induction w) auto

lemma input_tape_def: "<w>\<^sub>t\<^sub>p = (if w = [] then \<langle>\<rangle> else \<langle>|Some (hd w)|map Some (tl w)\<rangle>)"
  by (induction w) auto

lemma input_tape_size: "w \<noteq> [] \<Longrightarrow> tape_size <w>\<^sub>t\<^sub>p = length w"
  unfolding tape_size_def by (induction w) auto


text\<open>By convention, the initial configuration has the input word on the first tape
  with all other tapes being empty.\<close>

definition initial_config :: "'s list \<Rightarrow> ('q, 's) TM_config"
  where [simp]: "initial_config w = conf q\<^sub>0 (<w>\<^sub>t\<^sub>p # empty_tape \<up> (k - 1))"

lemma wf_initial_config[intro]: "wf_config (initial_config w)" using at_least_one_tape by simp


subsubsection\<open>Output\<close>

text\<open>By convention, the \<^emph>\<open>output\<close> of a TM is found on its last tape
  when the computation has reached its end.
  The tape head is positioned over the first symbol of the word,
  and the \<open>n\<close>-th symbol of the word is reached by moving the tape head \<open>n\<close> cells to the right.
  As with input, the \<^const>\<open>blank_symbol\<close> is not part of the output,
  so only the symbols up to the first blank will be considered output.\<close> (* TODO does this make sense *)

definition output_config :: "('q, 's) TM_config \<Rightarrow> 's list"
  where "output_config c = (let o_tp = last (tapes c) in
    case head o_tp of Bk \<Rightarrow> [] | Some h \<Rightarrow> h # the (those (takeWhile (\<lambda>s. s \<noteq> Bk) (right o_tp))))"

lemma out_config_simps[simp]: "last (tapes c) = <w>\<^sub>t\<^sub>p \<Longrightarrow> output_config c = w"
  unfolding output_config_def by (induction w) (auto simp add: takeWhile_map)


subsubsection\<open>Running a TM Program\<close>

definition run :: "nat \<Rightarrow> 's list \<Rightarrow> ('q, 's) TM_config"
  where "run n w \<equiv> steps n (initial_config w)"

corollary wf_config_run: "wf_config (run n w)" unfolding run_def by blast


definition compute :: "'s list \<Rightarrow> 's list option"
  where "compute w \<equiv> if \<exists>n. is_final (run n w)
    then Some (output_config (run (LEAST n. is_final (run n w)) w))
    else None"

lemma compute_eqI:
  assumes "is_final (run n w)"
  shows "compute w = Some (output_config (run n w))"
proof -
  from assms have *: "run (LEAST n. is_final (run n w)) w = run n w" unfolding run_def by blast
  from assms show ?thesis unfolding compute_def * by presburger
qed

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>

end
