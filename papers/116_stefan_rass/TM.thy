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
lemma M_rec[simp]: "M_rec = \<lparr> TM_record.tape_count = k,
    states = Q, initial_state = q\<^sub>0, final_states = F, accepting_states = F\<^sup>+,
    next_state = \<delta>\<^sub>q, next_write = \<delta>\<^sub>w, next_move  = \<delta>\<^sub>m \<rparr>"
    unfolding TM_fields_defs by simp


subsubsection\<open>Properties\<close>

sublocale is_valid_TM M_rec using Rep_TM .. \<comment> \<open>The axioms of \<^locale>\<open>is_valid_TM\<close> hold by definition.\<close>

lemmas at_least_one_tape = at_least_one_tape[folded TM_fields_defs]
lemmas state_axioms = state_axioms[folded TM_fields_defs]
lemmas TM_axioms = at_least_one_tape state_axioms

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

text\<open>We define a TM \<^emph>\<open>configuration\<close> as a record of:\<close>

record ('q, 's) TM_config =
  state :: 'q \<comment> \<open>the current state\<close>
  tapes :: "'s tape list" \<comment> \<open>a vector of tapes\<close>

text\<open>Combined with the \<^typ>\<open>('q, 's) TM\<close> definition, it completely describes a TM at any time during its execution.\<close>

definition heads :: "('q, 's) TM_config \<Rightarrow> 's tp_symbol list" \<comment> \<open>The vector of symbols currently under the TM-heads\<close>
  where [simp]: "heads c = map head (tapes c)"


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
  where [simp]: "wf_config c \<equiv> length (tapes c) = k"


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

lemma tape_shift_set: "set_tape (tape_shift m tp) = set_tape tp"
proof (induction tp)
  case (Tape l h r)
  show ?case
  proof (induction m)
    case Shift_Left show ?case by (induction l) auto next
    case Shift_Right show ?case by (induction r) auto
  qed simp
qed


text\<open>Write a symbol to the current position of the TM tape head.\<close>

definition tape_write :: "'s tp_symbol \<Rightarrow> 's tape \<Rightarrow> 's tape"
  where "tape_write s tp = \<langle>left tp|s|right tp\<rangle>"

corollary tape_write_simps[simp]: "tape_write s \<langle>l|h|r\<rangle> = \<langle>l|s|r\<rangle>" unfolding tape_write_def by simp


text\<open>Write a symbol, then move the head.\<close>

definition tape_action :: "('s tp_symbol \<times> head_move) \<Rightarrow> 's tape \<Rightarrow> 's tape"
  where "tape_action a tp = tape_shift (snd a) (tape_write (fst a) tp)"

corollary tape_action_altdef: "tape_action (s, m) = tape_shift m \<circ> tape_write s"
  unfolding tape_action_def by auto

end \<comment> \<open>\<^locale>\<open>TM_abbrevs\<close>\<close>


subsubsection\<open>Steps\<close>

context TM
begin

text\<open>If the current state is not final,
  apply the action determined by \<^const>\<open>\<delta>\<close> for the current configuration.
  Otherwise, do not execute any action.\<close>

definition step_not_final :: "('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config"
  where [simp]: "step_not_final c = (let q=state c; hds=heads c in \<lparr>
      state = next_state q hds,
      tapes = map2 tape_action (next_actions q hds) (tapes c)
   \<rparr>)"

definition step :: "('q, 's) TM_config \<Rightarrow> ('q, 's) TM_config"
  where [simp]: "step c = (if state c \<in> F then c else step_not_final c)"

abbreviation "steps n \<equiv> step ^^ n"

corollary step_simps:
  shows step_final: "is_final c \<Longrightarrow> step c = c"
    and step_not_final: "\<not> is_final c \<Longrightarrow> step c = step_not_final c"
  unfolding step_def by auto


paragraph\<open>Final Steps\<close>

lemma final_steps[simp, intro]: "is_final c \<Longrightarrow> steps n c = c"
  by (rule funpow_fixpoint) (rule step_final)

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

corollary final_mono': "mono (\<lambda>n. is_final ((step^^n) c))"
  using final_mono by (intro monoI le_boolI)


paragraph\<open>Well-Formed Steps\<close>

lemma wf_step_not_final: "wf_config c \<Longrightarrow> wf_config (step_not_final c)"
  unfolding wf_config_def step_not_final_def Let_def TM_config.simps
  unfolding length_map length_zip next_actions_length by simp

lemma wf_step[intro]: "wf_config c \<Longrightarrow> wf_config (step c)"
  unfolding step_def using wf_step_not_final by presburger

lemma funpow_induct: "P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> P (f x)) \<Longrightarrow> P ((f^^n) x)"
  by (induction n) auto

corollary wf_steps[intro]: "wf_config c \<Longrightarrow> wf_config (steps n c)"
  using wf_step by (elim funpow_induct)


subsubsection\<open>Running a TM Program\<close>

text\<open>TM execution begins with the head at the start of the input word.\<close>

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


definition initial_config :: "'s list \<Rightarrow> ('q, 's) TM_config"
  where [simp]: "initial_config w = \<lparr> state = q\<^sub>0, tapes = <w>\<^sub>t\<^sub>p # empty_tape \<up> (k - 1) \<rparr>"

definition run :: "nat \<Rightarrow> 's list \<Rightarrow> ('q, 's) TM_config"
  where [simp]: "run n w \<equiv> steps n (initial_config w)"


lemma wf_initial_config[intro]: "wf_config (initial_config w)" using at_least_one_tape by simp

corollary wf_config_run: "wf_config (run n w)" unfolding run_def by blast

end \<comment> \<open>\<^locale>\<open>TM\<close>\<close>


subsection \<open>Composition of Turing Machines\<close>

\<comment> \<open>Let M1 be a k1-tape TM, M2 a k2-tape TM. We define the composition of M1 and M2
    as a (k1+k2-1)-tape TM. First M1 operates on the tapes 0,1,...,k1-1.
    When M1 finishes, M2 operates on the tapes 0,k1,k1+1,...,k1+k2-2.
    Therefore, M1 is expected to write its output (M2's input) on the zeroth tape.\<close>

definition tm_comp :: "('q1, 's) TM \<Rightarrow> ('q2, 's) TM \<Rightarrow> ('q1+'q2, 's) TM" ("_ |+| _" [0, 0] 100)
  where "tm_comp M1 M2 = (let k = tape_count M1 + tape_count M2 - 1 in \<lparr>
    tape_count = k,
    states = states M1 <+> states M2,
    initial_state = Inl (initial_state M1),
    final_states = Inr ` final_states M2,
    accepting_states = Inr ` accepting_states M2,
    symbols = symbols M1 \<union> symbols M2,
    next_state = (\<lambda>q w. case q of
                        Inl q1 \<Rightarrow> let w1 = nths w {0..<tape_count M1} in
                                  let q' = next_state M1 q1 w1 in
                                  if q' \<in> final_states M1
                                    then Inr (initial_state M2)
                                    else Inl q'
                      | Inr q2 \<Rightarrow> let w2 = nths w ({0} \<union> {tape_count M1..<k}) in
                                  Inr (next_state M2 q2 w2)
                 ),
    next_action = (\<lambda>q w. case q of
                         Inl q1 \<Rightarrow> let w1 = nths w {0..<tape_count M1} in
                                   pad k Nop (next_action M1 q1 w1)
                       | Inr q2 \<Rightarrow> let w2 = nths w ({0} \<union> {tape_count M1..<k}) in
                                   let a2 = next_action M2 q2 w2 in
                                   hd a2 # Nop \<up> (tape_count M1 - 1) @ tl a2
                        )
  \<rparr>)"

lemma tm_comp_simps[simp]:
  fixes M1 M2
  defines "M \<equiv> M1 |+| M2"
    and "k1 \<equiv> tape_count M1" and "k2 \<equiv> tape_count M2"
  defines "k \<equiv> k1 + k2 - 1"
  shows     "tape_count M = k"
                "states M = states M1 <+> states M2"
           "initial_state M = Inl (initial_state M1)"
          "final_states M = Inr ` final_states M2"
      "accepting_states M = Inr ` accepting_states M2"
               "symbols M = symbols M1 \<union> symbols M2"
   "next_state M (Inl q1) = (\<lambda>w. let q' = next_state M1 q1 (nths w {0..<k1}) in
                                   if q' \<in> final_states M1 then Inr (initial_state M2) else Inl q')"
   "next_state M (Inr q2) = (\<lambda>w. Inr (next_state M2 q2 (nths w ({0} \<union> {k1..<k}))))"
  "next_action M (Inl q1) = (\<lambda>w. pad k Nop (next_action M1 q1 (nths w {0..<k1})))"
  "next_action M (Inr q2) = (\<lambda>w. let a2 = next_action M2 q2 (nths w ({0} \<union> {k1..<k})) in
                                   hd a2 # Nop \<up> (k1 - 1) @ tl a2)"
  unfolding M_def k_def k1_def k2_def
  unfolding tm_comp_def[unfolded Let_def] Let_def sum.case TM.TM.simps by (fact refl)+

lemma tm_comp_simps':
  fixes M1 M2
  defines "M \<equiv> M1 |+| M2"
    and "k \<equiv> tape_count M1 + tape_count M2 - 1"
  shows "next_state M = (\<lambda>q w. case q of
                              Inl q1 \<Rightarrow> let w1 = nths w {0..<tape_count M1};
                                            q' = next_state M1 q1 w1 in
                                          if q' \<in> final_states M1
                                            then Inr (initial_state M2)
                                            else Inl q'
                            | Inr q2 \<Rightarrow> let w2 = nths w ({0} \<union> {tape_count M1..<k}) in
                                          Inr (next_state M2 q2 w2) )"
       "next_action M = (\<lambda>q w. case q of
                          Inl q1 \<Rightarrow> let w1 = nths w {0..<tape_count M1} in
                                      pad k Nop (next_action M1 q1 w1)
                        | Inr q2 \<Rightarrow> let w2 = nths w ({0} \<union> {tape_count M1..<k});
                                        a2 = next_action M2 q2 w2 in
                                      hd a2 # Nop \<up> (tape_count M1 - 1) @ tl a2 )"
  unfolding M_def k_def tm_comp_def[unfolded Let_def] Let_def TM.TM.simps by (fact refl)+


lemma tm_comp_tape_count:
  fixes M1 M2
  defines "M \<equiv> M1 |+| M2"
  shows "TM M2 \<Longrightarrow> tape_count M1 \<le> tape_count M"
    and "TM M1 \<Longrightarrow> tape_count M2 \<le> tape_count M"
proof -
  assume "TM M2"
  from \<open>TM M2\<close>[THEN TM.at_least_one_tape] show "tape_count M1 \<le> tape_count M"
    unfolding M_def tm_comp_simps using le_add1 by (subst diff_add_assoc)
next
  assume "TM M1"
  from \<open>TM M1\<close>[THEN TM.at_least_one_tape] show "tape_count M2 \<le> tape_count M"
    unfolding M_def tm_comp_simps using le_add1 by (subst add.commute) (subst diff_add_assoc)
qed

lemma tm_comp_cases [consumes 4, case_names wfs1 wfs2]:
  fixes M1 M2 P
  defines "k1 \<equiv> tape_count M1" and "k2 \<equiv> tape_count M2"
  defines "k \<equiv> tape_count M1 + tape_count M2 - 1"
  defines "M \<equiv> M1 |+| M2"
  assumes wf: "TM M1" "TM M2"
    and symbols_eq: "symbols M1 = symbols M2"
  assumes wfs: "pre_TM.wf_state M q w"
  assumes q1: "\<And>q1 w. q = (Inl q1) \<Longrightarrow> pre_TM.wf_state M1 q1 (nths w {0..<k1}) \<Longrightarrow> P (Inl q1) w"
  assumes q2: "\<And>q2 w. q = (Inr q2) \<Longrightarrow> pre_TM.wf_state M2 q2 (nths w ({0} \<union> {k1..<k})) \<Longrightarrow> P (Inr q2) w"
  shows "P q w"
  using wfs
proof (cases q)
  case (Inl q1)
  from wfs show "P q w" unfolding \<open>q = Inl q1\<close>
  proof (intro q1[OF \<open>q = Inl q1\<close>], unfold pre_TM.wf_state_def, elim conjE, intro conjI)
    assume "Inl q1 \<in> states M"
    then show "q1 \<in> states M1" unfolding M_def tm_comp_simps by blast

    assume len_w: "length w = tape_count M"
    from tm_comp_tape_count(1)[OF wf(2)] show "length (nths w {0..<k1}) = tape_count M1"
      unfolding M_def length_nths_interval len_w k1_def by (subst min_absorb2) auto

    have "set (nths w {0..<k1}) \<subseteq> set w" by (fact set_nths_subset)
    also assume "... \<subseteq> symbols M"
    also have "... \<subseteq> symbols M1" unfolding M_def tm_comp_simps symbols_eq by blast
    finally show "set (nths w {0..<k1}) \<subseteq> symbols M1" .
  qed
next
  case (Inr q2)
  from wfs show "P q w" unfolding \<open>q = Inr q2\<close>
  proof (intro q2[OF \<open>q = Inr q2\<close>], unfold pre_TM.wf_state_def, elim conjE, intro conjI)
    assume "Inr q2 \<in> states M"
    then show "q2 \<in> states M2" unfolding M_def tm_comp_simps by blast

    assume len_w: "length w = tape_count M"

    have "1 \<le> length w" unfolding len_w M_def tm_comp_simps
      using wf[THEN TM.at_least_one_tape] by linarith
    have "1 \<le> k1" unfolding k1_def by (fact wf(1)[THEN TM.at_least_one_tape])
    have "1 \<le> k2" unfolding k2_def by (fact wf(2)[THEN TM.at_least_one_tape])

    have "length (nths w ({0} \<union> {k1..<k})) = min (length w) k - k1 + 1"
      unfolding nths_insert_interval_less[OF \<open>1 \<le> length w\<close> \<open>1 \<le> k1\<close>]
      unfolding length_Cons length_nths_interval by simp
    also have "... = k1 + k2 - 1 - k1 + 1"
      unfolding len_w M_def tm_comp_simps
      unfolding k_def k1_def k2_def min.idem ..
    also have "... = k2" using TM.at_least_one_tape[OF wf(2), folded k2_def] by simp
    finally show "length (nths w ({0} \<union> {k1..<k})) = tape_count M2" unfolding k2_def .

     have "set (nths w ({0} \<union> {k1..<k})) \<subseteq> set w" by (fact set_nths_subset)
    also assume "... \<subseteq> symbols M"
    also have "... \<subseteq> symbols M2" unfolding M_def tm_comp_simps symbols_eq by blast
    finally show "set (nths w ({0} \<union> {k1..<k})) \<subseteq> symbols M2" .
  qed
qed

lemma (in TM) sw_Nop_k: "symbol_of_write ` set (Nop \<up> n) \<subseteq> symbols M"
  using symbol_axioms(2) set_replicate_subset by force

lemma wf_tm_comp:
  fixes M1 :: "('q1, 's) TM" and M2 :: "('q2, 's) TM"
  assumes wf: "TM M1" "TM M2"
    and symbols_eq[simp]: "symbols M1 = symbols M2"
  shows "TM (M1 |+| M2)" (is "TM ?M")
proof (intro TM.intro; (elim tm_comp_cases[OF assms])?)
  let ?k1 = "tape_count M1" and ?k2 = "tape_count M2"
  let ?k = "?k1 + ?k2 - 1"

  interpret M1: TM M1 by fact
  interpret M2: TM M2 by fact

  from M2.at_least_one_tape have "tape_count ?M \<ge> ?k1"
    unfolding tm_comp_simps using le_add1 by (subst diff_add_assoc)
  with M1.at_least_one_tape show "tape_count ?M \<ge> 1" by (fact le_trans)
  from M1.state_axioms(1) M2.state_axioms(1) show "finite (states ?M)" by simp
  from M1.state_axioms(2) show "initial_state ?M \<in> states ?M" by auto
  from M2.state_axioms(3) show "final_states ?M \<subseteq> states ?M" by auto
  from M2.state_axioms(4) show "accepting_states ?M \<subseteq> final_states ?M" by auto
  from M1.symbol_axioms(1) show "finite (symbols ?M)" by simp
  from M1.symbol_axioms(2) show "Bk \<in> symbols ?M" by simp

  (* case distinction on q *)
  fix w :: "'s list" and q :: "'q1 + 'q2"
  {
    fix q1 (* case M1: "q = Inl q1" *)
    assume "q = Inl q1" and wfs1: "M1.wf_state q1 (nths w {0..<?k1})"

    show "next_state ?M (Inl q1) w \<in> states ?M" unfolding tm_comp_simps Let_def
    proof (rule if_cases)
      show "Inr (initial_state M2) \<in> states M1 <+> states M2"
        using TM.state_axioms(2)[OF wf(2)] by blast
      show "Inl (next_state M1 q1 (nths w {0..<?k1})) \<in> states M1 <+> states M2"
        using TM.next_state[OF wf(1) wfs1] by blast
    qed

    show "length (next_action ?M (Inl q1) w) = tape_count ?M"
      using tm_comp_tape_count(1)[OF wf(2), of M1]
      unfolding tm_comp_simps pad_length
      unfolding M1.next_action_length[OF wfs1] by (fact max_absorb1)

    show "symbol_of_write ` set (next_action ?M (Inl q1) w) \<subseteq> symbols ?M"
      unfolding tm_comp_simps set_append image_Un
    proof (intro Un_mono)
      show "symbol_of_write ` set (next_action M1 q1 (nths w {0..<?k1})) \<subseteq> symbols M1"
        by (fact M1.next_write_symbol[OF wfs1])
      show "symbol_of_write ` set (Nop \<up> n) \<subseteq> symbols M2" for n by (fact M2.sw_Nop_k)
    qed

    assume "q \<in> final_states ?M" (* this is only ever true if q represents a state of M2 *)
    then have False unfolding \<open>q = Inl q1\<close> tm_comp_simps by blast
    then show "next_state ?M (Inl q1) w = Inl q1"
      and "set (next_action ?M (Inl q1) w) \<subseteq> {Nop}" by blast+
  }

  {
    fix q2 (* case M2: "q = Inr q2" *)
    assume "q = Inr q2" and wfs2: "M2.wf_state q2 (nths w ({0} \<union> {?k1..<?k}))"

    show "next_state ?M (Inr q2) w \<in> states ?M" unfolding tm_comp_simps
      using TM.next_state[OF wf(2) wfs2] by blast

    have "length (next_action ?M (Inr q2) w) = ?k1 - 1 + (?k2 - 1) + 1"
      unfolding tm_comp_simps Let_def
      unfolding list.size length_append length_replicate length_tl
      unfolding M2.next_action_length[OF wfs2]
      by presburger
    also have "... = ?k - 1 + 1"
      unfolding add_diff_assoc2[OF M1.at_least_one_tape] add_diff_assoc[OF M2.at_least_one_tape] ..
    also have "... = tape_count ?M"
      using \<open>tape_count ?M \<ge> 1\<close> unfolding tm_comp_simps by (fact diff_add)
    finally show "length (next_action ?M (Inr q2) w) = tape_count ?M" .

    define xs where xs: "xs \<equiv> next_action M2 q2 (nths w ({0} \<union> {?k1..<?k}))"
    define ys :: "'s action list" where ys: "ys \<equiv> Nop \<up> (?k1 - 1)"
    have sna: "set (next_action ?M (Inr q2) w) = set xs \<union> set ys"
    proof -
      have "length xs \<ge> 1" unfolding xs M2.next_action_length[OF wfs2]
        by (fact M2.at_least_one_tape)
      then have "xs \<noteq> []" by auto

      have "set (next_action ?M (Inr q2) w) = set (hd xs # ys @ tl xs)"
        unfolding tm_comp_simps Let_def set_append
        unfolding xs[symmetric] ys[symmetric] ..
      also have "set (hd xs # ys @ tl xs) = insert (hd xs) (set (ys @ tl xs))" by simp
      also have "... = insert (hd xs) (set (tl xs @ ys))" by force
      also have "... = set ((hd xs # tl xs) @ ys)" by force
      also have "... = set (hd xs # tl xs) \<union> set ys" by simp
      also have "... = set xs \<union> set ys" using \<open>xs \<noteq> []\<close> by force
      finally show "set (next_action ?M (Inr q2) w) = set xs \<union> set ys" .
    qed
    then have "symbol_of_write ` set (next_action ?M (Inr q2) w) = symbol_of_write ` (set xs \<union> set ys)"
      by (rule arg_cong)
    also have "... = symbol_of_write ` set xs \<union> symbol_of_write ` set ys" by (fact image_Un)
    also have "... \<subseteq> symbols ?M" unfolding tm_comp_simps symbols_eq
    proof (intro Un_mono)
      from wfs2 show "symbol_of_write ` set xs \<subseteq> symbols M2"
        unfolding xs by (fact M2.next_write_symbol)
      have "symbol_of_write ` set ys \<subseteq> {Bk}" unfolding ys by force
      also have "... \<subseteq> symbols M2" using M2.symbol_axioms(2) by blast
      finally show "symbol_of_write ` set ys \<subseteq> symbols M2" .
    qed
    finally show "symbol_of_write ` set (next_action ?M (Inr q2) w) \<subseteq> symbols ?M" .


    assume "q \<in> final_states ?M"
    then have qf: "q2 \<in> final_states M2" unfolding \<open>q = Inr q2\<close> tm_comp_simps by blast

    show "next_state ?M (Inr q2) w = Inr q2" unfolding tm_comp_simps M2.final_state[OF wfs2 qf] ..
    show "set (next_action ?M (Inr q2) w) \<subseteq> {Nop}" unfolding sna
    proof (intro Un_least)
      from wfs2 qf show "set xs \<subseteq> {Nop}" unfolding xs by (fact M2.final_action)
      show "set ys \<subseteq> {Nop}" unfolding ys by (fact set_replicate_subset)
    qed
  }
qed


definition simple_alphabet_lift where
  "simple_alphabet_lift M \<Sigma> \<equiv>
    M\<lparr>
          symbols := symbols M \<union> \<Sigma>,
       next_state := (\<lambda>q w. if set w \<subseteq> symbols M
                              then next_state M q w
                              else q),
      next_action := (\<lambda>q w. if set w \<subseteq> symbols M
                              then next_action M q w
                              else Nop \<up> tape_count M)
    \<rparr>"

lemma (in TM) wf_alphabet_lift:
  assumes "finite \<Sigma>'"
  shows "TM (simple_alphabet_lift M \<Sigma>')"
  unfolding simple_alphabet_lift_def using TM_axioms
proof (induction M)
  case (fields k Z q0 F Fa \<Sigma> \<delta>s \<delta>a)
  let ?M = "\<lparr>tape_count = k, states = Z, initial_state = q0, final_states = F,
    accepting_states = Fa, symbols = \<Sigma>, next_state = \<delta>s, next_action = \<delta>a\<rparr>"
  interpret M: TM ?M by fact

  let ?M' = "\<lparr>tape_count = k, states = Z, initial_state = q0, final_states = F,
    accepting_states = Fa, symbols = \<Sigma> \<union> \<Sigma>',
    next_state = \<lambda>q w. if set w \<subseteq> \<Sigma> then \<delta>s q w else q,
    next_action = \<lambda>q w. if set w \<subseteq> \<Sigma> then \<delta>a q w else Nop \<up> k\<rparr>"

  show ?case proof (intro TM.intro, unfold TM.TM.simps)
    show "1 \<le> k" using M.at_least_one_tape unfolding TM.TM.simps .
    show "finite Z" "q0 \<in> Z" "F \<subseteq> Z" "Fa \<subseteq> F" using M.state_axioms unfolding TM.TM.simps .
    show "finite (\<Sigma> \<union> \<Sigma>')" using M.symbol_axioms(1) assms unfolding TM.TM.simps by (fact finite_UnI)
    show "Bk \<in> \<Sigma> \<union> \<Sigma>'" using M.symbol_axioms(2) unfolding TM.TM.simps ..

    fix q w
    assume wfs: "pre_TM.wf_state ?M' q w"
    then have "q \<in> Z" "length w = k" "set w \<subseteq> \<Sigma> \<union> \<Sigma>'"
      unfolding pre_TM.wf_state_def TM.TM.simps by blast+
    then have wfI: "set w \<subseteq> \<Sigma> \<Longrightarrow> M.wf_state q w" unfolding M.wf_state_def TM.TM.simps by blast

    show "(if set w \<subseteq> \<Sigma> then \<delta>s q w else q) \<in> Z"
    proof (rule ifI)
      show "set w \<subseteq> \<Sigma> \<Longrightarrow> \<delta>s q w \<in> Z" by (intro M.next_state[unfolded TM.TM.simps] wfI)
      show "q \<in> Z" by fact
    qed

    show "length (if set w \<subseteq> \<Sigma> then \<delta>a q w else Nop \<up> k) = k"
    proof (rule ifI)
      show "set w \<subseteq> \<Sigma> \<Longrightarrow> length (\<delta>a q w) = k"
        by (intro M.next_action_length[unfolded TM.TM.simps] wfI)
      show "length (Nop \<up> k) = k" by (fact length_replicate)
    qed

    show "symbol_of_write ` set (if set w \<subseteq> \<Sigma> then \<delta>a q w else Nop \<up> k) \<subseteq> \<Sigma> \<union> \<Sigma>'"
    proof (rule ifI)
      show "set w \<subseteq> \<Sigma> \<Longrightarrow> symbol_of_write ` set (\<delta>a q w) \<subseteq> \<Sigma> \<union> \<Sigma>'"
        using M.next_write_symbol[OF wfI] unfolding TM.TM.simps by blast
      show "symbol_of_write ` set (Nop \<up> k) \<subseteq> \<Sigma> \<union> \<Sigma>'"
        using M.sw_Nop_k unfolding TM.TM.simps by fast
    qed

    assume "q \<in> F"

    show "(if set w \<subseteq> \<Sigma> then \<delta>s q w else q) = q"
    proof (rule ifI)
      show "set w \<subseteq> \<Sigma> \<Longrightarrow> \<delta>s q w = q"
        using M.final_state[OF wfI] \<open>q \<in> F\<close> unfolding TM.TM.simps by blast
      show "q = q" ..
    qed
    show "set (if set w \<subseteq> \<Sigma> then \<delta>a q w else Nop \<up> k) \<subseteq> {Nop}"
    proof (rule ifI)
      show "set w \<subseteq> \<Sigma> \<Longrightarrow> set (\<delta>a q w) \<subseteq> {Nop}"
        using M.final_action[OF wfI] \<open>q \<in> F\<close> unfolding TM.TM.simps by blast
      show "set (Nop \<up> k) \<subseteq> {Nop}" by (fact set_replicate_subset)
    qed
  qed
qed

definition lift_tm_comp where
  "lift_tm_comp M1 M2 \<equiv> tm_comp (simple_alphabet_lift M1 (symbols M2))
                                (simple_alphabet_lift M2 (symbols M1))"

lemma wf_lift_tm_comp:
  assumes wf: "TM M1" "TM M2"
  shows "TM (lift_tm_comp M1 M2)"
  unfolding lift_tm_comp_def
proof (rule wf_tm_comp)
  let ?M1 = "simple_alphabet_lift M1 (symbols M2)"
  let ?M2 = "simple_alphabet_lift M2 (symbols M1)"

  interpret M1: TM M1 by fact
  interpret M2: TM M2 by fact

  show "TM (simple_alphabet_lift M1 (symbols M2))"
    using wf(1) M2.symbol_axioms(1) by (fact TM.wf_alphabet_lift)
  show "TM (simple_alphabet_lift M2 (symbols M1))"
    using wf(2) M1.symbol_axioms(1) by (fact TM.wf_alphabet_lift)

  show "symbols ?M1 = symbols ?M2" unfolding simple_alphabet_lift_def TM.TM.simps by auto
qed


hide_const (open) "TM.action.L" "TM.action.R" "TM.action.W"


subsection \<open>Hoare Rules\<close>

type_synonym ('q, 's) assert = "('q, 's) TM_config \<Rightarrow> bool"

definition (in TM) hoare_halt :: "('q, 's) assert \<Rightarrow> ('q, 's) assert \<Rightarrow> bool" where
  "hoare_halt P Q \<longleftrightarrow> (\<forall>c. wf_config c \<longrightarrow> P c \<longrightarrow>
    (\<exists>n. let cn = (step^^n) c in is_final cn \<and> Q cn))"

context TM begin
lemma hoare_haltI[intro]:
  fixes P Q
  assumes "\<And>c. wf_config c \<Longrightarrow> P c \<Longrightarrow>
             \<exists>n. let cn = (step^^n) c in is_final cn \<and> Q cn"
  shows "hoare_halt P Q"
  unfolding hoare_halt_def using assms by blast

lemma hoare_haltE[elim]:
  fixes c
  assumes "wf_config c" "P c"
      and "hoare_halt P Q"
    obtains n where "is_final ((step^^n) c)" and "Q ((step^^n) c)"
  using assms
  unfolding hoare_halt_def by meson

lemma hoare_contr:
  fixes P and c
  assumes "wf_config c" "P c" "hoare_halt P (\<lambda>_. False)"
  shows "False"
using assms by (rule hoare_haltE)

lemma hoare_true: "hoare_halt P Q \<Longrightarrow> hoare_halt P (\<lambda>_. True)"
  unfolding hoare_halt_def by metis

lemma hoare_and[intro]:
  assumes h1: "hoare_halt P Q1"
    and h2: "hoare_halt P Q2"
  shows "hoare_halt P (\<lambda>c. Q1 c \<and> Q2 c)"
proof
  fix c assume "P c" and wf: "wf_config c"
  from wf \<open>P c\<close> h1 obtain n1 where fn1: "is_final ((step^^n1) c)" and q1: "Q1 ((step^^n1) c)"
    by (rule hoare_haltE)
  from wf \<open>P c\<close> h2 obtain n2 where fn2: "is_final ((step^^n2) c)" and q2: "Q2 ((step^^n2) c)"
    by (rule hoare_haltE)

  define n::nat where "n \<equiv> max n1 n2"
  hence "n1 \<le> n" "n2 \<le> n" by simp+

  from wf \<open>n1 \<le> n\<close> fn1 have steps1: "((step^^n) c) = ((step^^n1) c)" by (fact final_le_steps)
  from wf \<open>n2 \<le> n\<close> fn2 have steps2: "((step^^n) c) = ((step^^n2) c)" by (fact final_le_steps)
  from fn1 q1 q2 have "let qn=(step^^n) c in is_final qn \<and> Q1 qn \<and> Q2 qn"
    by (fold steps1 steps2) simp
  thus "\<exists>n. let cn = (step ^^ n) c in is_final cn \<and> Q1 cn \<and> Q2 cn" ..
qed

abbreviation (input) init where "init w \<equiv> (\<lambda>c. c = initial_config w)"

definition halts :: "'s list \<Rightarrow> bool"
  where "halts w \<equiv> wf_word w \<and> hoare_halt (init w) (\<lambda>_. True)"

lemma halts_I[intro]: "wf_word w \<Longrightarrow> \<exists>n. is_final (run n w) \<Longrightarrow> halts w"
  unfolding halts_def hoare_halt_def by simp

lemma halts_D[dest]:
  assumes "halts w"
  shows "wf_word w"
    and "\<exists>n. is_final (run n w)"
  using assms hoare_halt_def wf_initial_config
  unfolding halts_def by fastforce+

lemma halts_altdef: "halts w \<longleftrightarrow> wf_word w \<and> (\<exists>n. is_final (run n w))" by blast

lemma hoare_halt_neg:
  assumes "\<not> hoare_halt (init w) Q"
    and "halts w"
  shows "hoare_halt (init w) (\<lambda>tp. \<not> Q tp)"
  using assms unfolding hoare_halt_def halts_def Let_def unfolding wf_config_def by fast

lemma halt_inj:
  assumes "wf_word w"
      and "hoare_halt (init w) (\<lambda>c. f c = x)"
      and "hoare_halt (init w) (\<lambda>c. f c = y)"
    shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  then have *: "a = x \<and> a = y \<longleftrightarrow> False" for a by blast

  from hoare_and assms(2-3) have "hoare_halt (init w) (\<lambda>c. f c = x \<and> f c = y)".
  then have "hoare_halt (init w) (\<lambda>_. False)" unfolding * .
  thus False using hoare_contr wf_initial_config[OF assms(1)] by fastforce
qed

end

definition "input_assert (P::'s list \<Rightarrow> bool) \<equiv> \<lambda>c::('q, 's::finite) TM_config.
              let tp = hd (tapes c) in P (head tp # right tp) \<and> left tp = []"

lemma hoare_comp:
  fixes M1 :: "('q1, 's) TM" and M2 :: "('q2, 's) TM"
    and Q :: "'s list \<Rightarrow> bool"
  assumes "TM.hoare_halt M1 (input_assert P) (input_assert Q)"
      and "TM.hoare_halt M2 (input_assert Q) (input_assert S)"
    shows "TM.hoare_halt (M1 |+| M2) (input_assert P) (input_assert S)"
sorry

subsection\<open>Deciding Languages\<close>

abbreviation input where "input w \<equiv> (\<lambda>c. hd (tapes c) = <w>\<^sub>t\<^sub>p)"

context TM begin

abbreviation "good_assert P \<equiv> \<forall>w. P (trim Bk w) = P w"

lemma good_assert_single: "good_assert P \<Longrightarrow> P [Bk] = P []"
proof -
  assume "good_assert P"
  hence "P (trim Bk [Bk]) = P [Bk]" ..
  thus ?thesis by simp
qed

lemma input_tp_assert:
  assumes "good_assert P"
  shows "P w \<longleftrightarrow> input_assert P (initial_config w)"
proof (cases "w = []")
  case True
  then show ?thesis
    unfolding input_assert_def initial_config_def apply simp
    using good_assert_single[OF assms] ..
next
  case False
  then show ?thesis
    unfolding input_assert_def initial_config_def apply simp
    using input_tape_right by metis
qed

lemma init_input: "init w c \<Longrightarrow> input w c"
  unfolding initial_config_def by simp

lemma init_state_initial_state: "init w c \<Longrightarrow> state c = initial_state M"
  unfolding initial_config_def by simp

definition accepts :: "'s list \<Rightarrow> bool"
  where "accepts w \<equiv> wf_word w \<and> hoare_halt (init w) (\<lambda>c. state c \<in> accepting_states M)"

lemma acceptsI[intro]:
  assumes "wf_word w"
    and "state (run n w) \<in> accepting_states M"
  shows "accepts w"
  using assms unfolding accepts_def hoare_halt_def
  by (meson state_axioms(4) subsetD)

lemma acceptsE[elim]:
  assumes "accepts w"
  obtains n where "state (run n w) \<in> accepting_states M"
using accepts_def assms hoare_halt_def wf_initial_config by fastforce

definition rejects :: "'s list \<Rightarrow> bool"
  where "rejects w \<equiv> wf_word w \<and> hoare_halt (init w) (\<lambda>c. state c \<in> rejecting_states M)"

lemma rejectsI[intro]:
  assumes "wf_word w"
    and "is_final (run n w)"
    and "state (run n w) \<in> rejecting_states M"
  shows "rejects w"
  using assms unfolding rejects_def hoare_halt_def
  by meson

lemma rejectsE[elim]:
  assumes "rejects w"
  obtains n where "is_final (run n w)"
    and "state (run n w) \<in> rejecting_states M"
by (smt (verit, ccfv_SIG) assms hoare_halt_def rejects_def wf_initial_config)

lemma halts_iff: "halts w \<longleftrightarrow> accepts w \<or> rejects w"
proof (intro iffI)
  assume "halts w"
  then obtain n where fin: "is_final (run n w)" and wf: "wf_word w" by blast
  thus "accepts w \<or> rejects w"
  proof (cases "state (run n w) \<in> accepting_states M")
    case True hence "accepts w"
      using fin wf acceptsI by blast
  next
    case False hence "rejects w"
      using fin wf rejectsI by blast
  qed blast+
next
  assume "accepts w \<or> rejects w" thus "halts w"
  unfolding accepts_def rejects_def halts_def using hoare_true by blast
qed

lemma acc_not_rej:
  assumes "accepts w"
  shows "\<not> rejects w"
proof (intro notI)
  assume "rejects w"

  have "hoare_halt (init w) (\<lambda>c. state c \<in> accepting_states M)"
    using \<open>accepts w\<close> unfolding accepts_def by (rule conjunct2)
  moreover have "hoare_halt (init w) (\<lambda>c. state c \<in> rejecting_states M)"
    using \<open>rejects w\<close> unfolding rejects_def by (rule conjunct2)
  ultimately have "hoare_halt (init w) (\<lambda>c. state c \<in> accepting_states M
                                          \<and> state c \<in> rejecting_states M)"
    by (fact hoare_and)
  then have "hoare_halt (init w) (\<lambda>c. False)" by auto

  moreover from assms have "wf_config (initial_config w)"
    unfolding accepts_def by (intro wf_initial_config) blast
  moreover have "init w (initial_config w)" ..
  ultimately show False by (intro hoare_contr)
qed

lemma rejects_altdef:
  "rejects w = (halts w \<and> \<not> accepts w)"
  using acc_not_rej halts_iff by blast

definition decides_word :: "'s lang \<Rightarrow> 's list \<Rightarrow> bool"
  where decides_def[simp]: "decides_word L w \<equiv> (w \<in> L \<longleftrightarrow> accepts w) \<and> (w \<notin> L \<longleftrightarrow> rejects w)"

abbreviation decides :: "'s lang \<Rightarrow> bool"
  where "decides L \<equiv> wf_lang L \<and> (\<forall>w\<in>wf_words. decides_word L w)"

lemma decides_halts: "decides_word L w \<Longrightarrow> halts w"
  by (cases "w \<in> L") (simp add: halts_iff)+

corollary decides_halts_all: "decides L \<Longrightarrow> \<forall>w\<in>wf_words. halts w"
  using decides_halts by blast

lemma decides_altdef:
  "decides_word L w \<longleftrightarrow> halts w \<and> (w \<in> L \<longleftrightarrow> accepts w)"
proof (intro iffI)
  fix w
  assume "decides_word L w"
  hence "halts w" by (rule decides_halts)
  moreover have "w \<in> L \<longleftrightarrow> accepts w" using \<open>decides_word L w\<close> by simp
  ultimately show "halts w \<and> (w \<in> L \<longleftrightarrow> accepts w)" ..
next
  assume "halts w \<and> (w \<in> L \<longleftrightarrow> accepts w)"
  then show "decides_word L w" by (simp add: rejects_altdef)
qed

lemma decides_altdef4: "decides_word L w \<longleftrightarrow> (if w \<in> L then accepts w else rejects w)"
  unfolding decides_def using acc_not_rej by (cases "w \<in> L") auto

lemma decides_altdef3: "decides_word L w \<longleftrightarrow> wf_word w \<and> hoare_halt (init w) (\<lambda>c. state c \<in> accepting_states M \<longleftrightarrow> w\<in>L)"
  unfolding decides_altdef4 accepts_def rejects_def
  by (cases "w\<in>L") (simp add: hoare_halt_def del: initial_config_def)+

end


subsection\<open>TM Languages\<close>

definition TM_lang :: "('q, 's) TM \<Rightarrow> 's lang" ("L'(_')")
  where "L(M) \<equiv> if (\<forall>w\<in>pre_TM.wf_words M. TM.halts M w)
                then {w\<in>pre_TM.wf_words M. TM.accepts M w}
                else undefined"

context TM begin

lemma decides_TM_lang_accepts: "(\<And>w. wf_word w \<Longrightarrow> halts w) \<Longrightarrow> decides {w. accepts w}"
  unfolding decides_def rejects_altdef accepts_def
  by (simp add: Collect_mono)

lemma decides_TM_lang: "(\<And>w. wf_word w \<Longrightarrow> halts w) \<Longrightarrow> decides L(M)"
  unfolding TM_lang_def using decides_TM_lang_accepts by auto

lemma decidesE: "decides L \<Longrightarrow> L(M) = L"
proof safe
  assume dec: "\<forall>w\<in>wf_words. decides_word L w"
  assume wfl: \<open>wf_lang L\<close>
  from dec have "\<forall>w\<in>wf_words. halts w"
    using decides_halts by blast
  then have L_M: "L(M) = {w\<in>wf_words. accepts w}" unfolding TM_lang_def by presburger

  fix w
  show "w \<in> L(M)" if "w \<in> L" proof -
    from \<open>w\<in>L\<close> wfl have "wf_word w" by blast
    moreover from \<open>w\<in>L\<close> \<open>wf_word w\<close> dec have "accepts w" unfolding decides_def by blast
    ultimately show "w \<in> L(M)" unfolding L_M by fastforce
  qed
  show "w \<in> L" if "w \<in> L(M)" proof -
    from \<open>w \<in> L(M)\<close> have "accepts w" "wf_word w" unfolding L_M by blast+
    with dec show "w \<in> L" unfolding decides_def by blast
  qed
qed

lemma TM_lang_unique: "\<exists>\<^sub>\<le>\<^sub>1L. wf_lang L \<and> decides L"
  using decidesE by (intro Uniq_I) metis

end


subsection\<open>Computation of Functions\<close>

context TM begin

definition computes_word :: "('s list \<Rightarrow> 's list) \<Rightarrow> 's list \<Rightarrow> bool"
  where computes_def[simp]: "computes_word f w \<equiv> hoare_halt (input w) (input (f w))"

abbreviation computes :: "('s list \<Rightarrow> 's list) \<Rightarrow> bool"
  where "computes f \<equiv> \<forall>w. computes_word f w"

end \<comment> \<open>context \<^locale>\<open>TM\<close>\<close>


subsection\<open>The Rejecting TM\<close>


locale Rej_TM =
  fixes \<Sigma> :: "'s set"
    and \<alpha> :: 'q
  assumes finite_alphabet: "finite \<Sigma>"
begin

definition Rejecting_TM :: "('q, 's) TM"
  where [simp]: "Rejecting_TM \<equiv> \<lparr>
    tape_count = 1,
    states = {\<alpha>},
    initial_state = \<alpha>,
    final_states = {\<alpha>},
    accepting_states = {},
    symbols = \<Sigma> \<union> {Bk},
    next_state = \<lambda>q w. \<alpha>,
    next_action = \<lambda>q w. [Nop]
  \<rparr>"

lemma wf_rej_TM: "TM Rejecting_TM"
  unfolding Rejecting_TM_def using finite_alphabet
  by unfold_locales simp_all

sublocale TM Rejecting_TM by (fact wf_rej_TM)

lemma rej_TM:
  assumes "set w \<subseteq> \<Sigma>"
  shows "rejects w"
  unfolding rejects_def
proof
  show "wf_word w" using assms by auto
next
  let ?rej = "rejecting_states Rejecting_TM"
  have final_rej: "?rej = final_states Rejecting_TM" by simp
  show "hoare_halt (init w) (\<lambda>c. state c \<in> ?rej)"
  proof
    fix c0
    assume "init w c0"
    then have "state c0 = initial_state Rejecting_TM" by (fact init_state_initial_state)
    then have "is_final ((step^^0) c0)" unfolding Rejecting_TM_def by simp
    then show "\<exists>n. let cn = (step ^^ n) c0 in is_final cn \<and> state cn \<in> ?rej"
      using final_rej by metis
  qed
qed

end \<comment> \<open>\<^locale>\<open>Rej_TM\<close>\<close>

lemma exists_wf_TM: "\<exists>M::('q, 's) TM. TM M"
proof
  fix \<alpha> :: 'q
  show "TM (Rej_TM.Rejecting_TM {} \<alpha>)" by (intro Rej_TM.wf_rej_TM) (unfold_locales, blast)
qed


subsection\<open>(nat, nat) TM\<close>
text \<open>Every well-formed TM is equivalent to some (nat, nat) TM\<close>

locale nat_TM = TM +
  fixes f :: "'q \<Rightarrow> nat" and f_inv
    and g :: "'s \<Rightarrow> nat" and g_inv
  defines "f \<equiv> SOME f. inj_on f (states M)"  and "f_inv \<equiv> inv_into (states M) f"
    and   "g \<equiv> SOME g. inj_on g (symbols M) \<and> g Bk = Bk" and "g_inv \<equiv> inv_into (symbols M) g"
begin

lemma f_inj: "inj_on f (states M)" unfolding f_def
  using countable_finite[OF state_axioms(1)] unfolding countable_def ..

lemma g_inj: "inj_on g (symbols M)" and g_Bk[simp]: "g Bk = Bk"
proof -
  from symbol_axioms(1) have "\<exists>g::'s \<Rightarrow> nat. inj_on g (symbols M) \<and> g Bk = Bk"
    by (fact finite_imp_inj_to_nat_fix_one)
  then have "inj_on g (symbols M) \<and> g Bk = Bk" unfolding g_def by (fact someI_ex)
  then show "inj_on g (symbols M)" and "g Bk = Bk" by auto
qed

definition natM :: "(nat, nat) TM" ("M\<^sub>\<nat>")
  where "natM \<equiv> \<lparr>
    tape_count = tape_count M,
    states = f ` states M,
    initial_state = f (initial_state M),
    final_states = f ` (final_states M),
    accepting_states = f ` (accepting_states M),
    symbols = g ` (symbols M),
    next_state = \<lambda>q w. f (next_state M (f_inv q) (map g_inv w)),
    next_action = \<lambda>q w. map (action_app g) (next_action M (f_inv q) (map g_inv w))
  \<rparr>"

lemma natM_simps[simp]:
  "tape_count natM = tape_count M"
  "states natM = f ` states M"
  "symbols natM = g ` symbols M"
  "accepting_states natM = f ` accepting_states M"
  unfolding natM_def by auto

lemma natM_rejecting_states[simp]:
  "rejecting_states natM = f ` rejecting_states M"
  unfolding natM_def apply simp
  by (metis Diff_subset f_inj inj_on_image_set_diff state_axioms(3) state_axioms(4) subset_trans)

lemma f_bij: "bij_betw f (states M) (states natM)" unfolding natM_simps
  using f_inj by (fact inj_on_imp_bij_betw)
lemma f_inv_bij: "bij_betw f_inv (states natM) (states M)" unfolding f_inv_def
  using f_bij by (fact bij_betw_inv_into)
lemma f_inv: "q \<in> states M \<Longrightarrow> f_inv (f q) = q" unfolding f_inv_def
  using f_inj by (rule inv_into_f_f)
lemma f_inv_img: "f_inv ` states natM = states M"
  using f_inj unfolding natM_simps f_inv_def by (fact inv_into_onto)
lemma inv_f: "q \<in> states natM \<Longrightarrow> f (f_inv q) = q"
  unfolding natM_simps f_inv_def by (fact f_inv_into_f)

lemma g_bij: "bij_betw g (symbols M) (symbols natM)" unfolding natM_simps
  using g_inj by (fact inj_on_imp_bij_betw)
lemma g_inv_bij: "bij_betw g_inv (symbols natM) (symbols M)" unfolding g_inv_def
  using g_bij by (fact bij_betw_inv_into)
lemma g_inv: "\<sigma> \<in> symbols M \<Longrightarrow> g_inv (g \<sigma>) = \<sigma>" unfolding g_inv_def
  using g_inj by (rule inv_into_f_f)
lemma g_inv_img: "g_inv ` g ` symbols M = symbols M"
  using g_inj unfolding g_inv_def by (fact inv_into_onto)
lemma inv_g: "\<sigma> \<in> symbols natM \<Longrightarrow> g (g_inv \<sigma>) = \<sigma>"
  unfolding natM_simps g_inv_def by (fact f_inv_into_f)
lemma g_inv_mem_eq: "\<sigma> \<in> symbols natM \<Longrightarrow> g_inv \<sigma> \<in> symbols M"
  unfolding g_inv_def natM_simps by (fact inv_into_into)

lemma map_g_inj: "inj_on (map g) wf_words"
  using g_inj list.inj_map_strong
  by (smt (verit, best) inj_on_def mem_Collect_eq subsetD)

sublocale pre_natM: pre_TM natM .

lemma g_inv_word_wf: "pre_natM.wf_word w \<Longrightarrow> wf_word (map g_inv w)"
proof simp
  assume "set w \<subseteq> g ` symbols M"
  then have "g_inv ` set w \<subseteq> g_inv ` g ` symbols M" by (fact image_mono)
  also have "... = symbols M" using g_inj unfolding g_inv_def by (fact inv_into_onto)
  finally show "g_inv ` set w \<subseteq> symbols M" .
qed

lemma f_inv_states: "q \<in> states natM \<Longrightarrow> f_inv q \<in> states M"
  unfolding natM_simps f_inv_def by (fact inv_into_into)

lemma map_g_bij: "bij_betw (map g) wf_words pre_natM.wf_words"
proof (intro bij_betw_imageI)
  show "(map g) ` (wf_words) = pre_natM.wf_words"
    unfolding natM_simps lists_eq_set[symmetric] lists_image ..
qed (fact map_g_inj)

lemma map_g_g_inv: "pre_natM.wf_word w \<Longrightarrow> map g (map g_inv w) = w"
  using g_inj g_inv_def map_map_inv_into_id by auto
lemma map_g_inv_g: "wf_word w' \<Longrightarrow> map g_inv (map g w') = w'"
  using g_inj g_inv_def map_inv_into_map_id by blast

lemma natM_wf_state_inv: "pre_natM.wf_state q w \<Longrightarrow> wf_state (f_inv q) (map g_inv w)"
proof (unfold pre_TM.wf_state_def, elim conjE, intro conjI)
  assume "q \<in> states natM" thus "f_inv q \<in> states M" by (fact f_inv_states)
  assume "length w = tape_count natM" thus "length (map g_inv w) = tape_count M" by force
  assume "pre_natM.wf_word w" thus "wf_word (map g_inv w)" by (fact g_inv_word_wf)
qed

lemma natM_wf_word: "wf_word w \<Longrightarrow> pre_natM.wf_word (map g w)" by auto


lemma wf_natM: "TM natM"
  apply unfold_locales
  unfolding natM_def
  using at_least_one_tape apply force
  using state_axioms(1) apply simp
  using state_axioms(2) apply simp
  using state_axioms(3) apply auto[1]
  using state_axioms(4) apply auto[1]
  using symbol_axioms(1) apply auto[1]
  apply simp using g_Bk symbol_axioms(2) apply force
  using next_state natM_wf_state_inv using natM_def apply force
  using next_action_length natM_wf_state_inv apply (simp add: natM_def)

  apply (unfold pre_TM.wf_state_def)[1] apply simp
  using symbol_action_app[of g, OF g_Bk] next_write_symbol
  apply (metis (no_types, lifting) f_inv_def g_inj g_inv_def inv_into_image_cancel inv_into_into length_map list.set_map pre_TM.wf_state_def subset_image_iff subset_trans)

  apply (fold natM_def)

  using final_state natM_wf_state_inv
  apply (smt (z3) TM.TM.select_convs(4) TM.TM.select_convs(7) f_inj f_inv_def image_iff natM_def state_axioms(3) subsetD inv_into_f_f)
proof -
  fix q w
  assume wfn: "pre_TM.wf_state natM q w" and finn: "q \<in> final_states natM"
  from wfn have wf: "wf_state (f_inv q) (map g_inv w)" by (rule natM_wf_state_inv)
  from finn have fin: "f_inv q \<in> final_states M"
    by (smt (verit, del_insts) TM.TM.select_convs(4) f_inj f_inv_def image_iff natM_def state_axioms(3) subsetD inv_into_f_f)
  from final_action[OF wf fin] action_app.simps(4)[of g]
  show "set (next_action M\<^sub>\<nat> q w) \<subseteq> {Nop}"
    unfolding natM_def by auto
qed

(* using the same name ("natM") for both sublocale and definition works,
 * since the sublocale is only used as namespace *)
sublocale natM: TM natM
  by (fact wf_natM)


fun config_conv :: "('q, 's) TM_config \<Rightarrow> (nat, nat) TM_config" ("C") where
  "config_conv \<lparr> state = q, tapes = tps \<rparr> =
          \<lparr> state = f q, tapes = map (tape_map g) tps \<rparr>"

fun config_conv_inv :: "(nat, nat) TM_config \<Rightarrow> ('q, 's) TM_config" ("C\<inverse>") where
  "config_conv_inv \<lparr> state = q, tapes = tps \<rparr> =
          \<lparr> state = f_inv q, tapes = map (tape_map g_inv) tps \<rparr>"

lemmas cc_simps = config_conv.simps config_conv_inv.simps

abbreviation config_conv_inv_and_conv ("CC") where "CC c \<equiv> C\<inverse> (C c)"
abbreviation config_conv_and_inv ("CC\<inverse>") where "CC\<inverse> c \<equiv> C (C\<inverse> c)"

lemma config_conv_state_inv:
  "q \<in> states M \<Longrightarrow> state (CC \<lparr> state = q, tapes = tps \<rparr>) = q"
  unfolding cc_simps TM.TM_config.simps(1) by (fact f_inv)

lemma tape_map_g_inv: "set_of_tape tp \<subseteq> symbols M \<Longrightarrow> (tape_map g_inv \<circ> tape_map g) tp = tp"
proof (induction tp)
  case (fields ls m rs)
  then have l: "set ls \<subseteq> symbols M" and m: "m \<in> symbols M" and r: "set rs \<subseteq> symbols M" by auto
  have *: "\<And>w. wf_word w \<Longrightarrow> map (\<lambda>x. g_inv (g x)) w = w" by (intro map_idI g_inv) blast
  show ?case unfolding comp_def tape_map.simps map_map unfolding *[OF l] *[OF r] g_inv[OF m] ..
qed

lemma config_conv_inv: "wf_config c \<Longrightarrow> CC c = c"
proof (induction c)
  case (fields q tps)
  let ?c = "\<lparr>state = q, tapes = tps\<rparr>"
  from \<open>wf_config ?c\<close> have "q \<in> states M"
    and tps_symbols: "list_all (\<lambda>tp. set_of_tape tp \<subseteq> symbols M) tps"
    unfolding wf_config_def Let_def TM_config.simps by blast+

  from \<open>q \<in> states M\<close> have "state (CC ?c) = state ?c" by (subst config_conv_state_inv) auto
  moreover have "tapes (CC ?c) = tapes ?c"
    unfolding cc_simps TM.TM_config.simps(2) map_map
  proof (intro map_idI)
    fix tp assume "tp \<in> set tps"
    with tps_symbols have "set_of_tape tp \<subseteq> symbols M" by blast
    then show "(tape_map g_inv \<circ> tape_map g) tp = tp" by (fact tape_map_g_inv)
  qed
  ultimately show ?case by (rule TM.TM_config.equality) simp
qed

lemma config_conv_state_inv':
  "q \<in> states natM \<Longrightarrow> state (CC\<inverse> \<lparr> state = q, tapes = tps \<rparr>) = q"
  unfolding cc_simps TM.TM_config.simps(1) f_inv_def
  using f_bij by (rule bij_betw_inv_into_right)

lemma config_conv_inv': "pre_natM.wf_config c \<Longrightarrow> CC\<inverse> c = c"
proof (induction c)
  case (fields q tps)
  let ?c = "\<lparr>state = q, tapes = tps\<rparr>"
  from \<open>pre_natM.wf_config ?c\<close> have "q \<in> states natM"
    and tps_symbols: "list_all (\<lambda>tp. set_of_tape tp \<subseteq> symbols natM) tps"
    unfolding pre_TM.wf_config_def Let_def TM_config.simps by blast+

  from \<open>q \<in> states natM\<close> have "state (CC\<inverse> ?c) = state ?c" by (subst config_conv_state_inv') auto
  moreover have "tapes (CC\<inverse> ?c) = tapes ?c"
    unfolding cc_simps TM.TM_config.simps(2) map_map
  proof (intro map_idI)
    fix tp assume "tp \<in> set tps"
    with tps_symbols have "set_of_tape tp \<subseteq> symbols natM" by blast
    then show "(tape_map g \<circ> tape_map g_inv) tp = tp"
    proof (induction tp)
      case (fields ls m rs)
      then have l: "set ls \<subseteq> symbols natM" and m: "m \<in> symbols natM" and r: "set rs \<subseteq> symbols natM" by auto
      have *: "\<And>w. pre_natM.wf_word w \<Longrightarrow> map (\<lambda>x. g (g_inv x)) w = w" by (intro map_idI inv_g) blast
      show ?case unfolding comp_def tape_map.simps map_map unfolding *[OF l] *[OF r] inv_g[OF m] ..
    qed
  qed
  ultimately show ?case by (rule TM.TM_config.equality) simp
qed

lemma wf_natM_config: "wf_config c \<Longrightarrow> pre_natM.wf_config (C c)"
proof (induction c)
  case (fields q tps)
  let ?c = "\<lparr>state = q, tapes = tps\<rparr>"
  from \<open>wf_config ?c\<close> show "pre_natM.wf_config (C ?c)"
  proof (elim wf_configE, intro pre_TM.wf_configI)
    assume "state ?c \<in> states M" thus "state (C ?c) \<in> states natM"
      unfolding cc_simps natM_simps TM_config.simps by (fact imageI)
    assume "length (tapes ?c) = tape_count M" thus "length (tapes (C ?c)) = tape_count natM"
      unfolding cc_simps natM_def TM.TM.simps TM_config.simps unfolding length_map .

    assume "\<forall>tp\<in>set (tapes ?c). set_of_tape tp \<subseteq> symbols M"
    then have wf_tp: "set_of_tape tp \<subseteq> symbols M" if "tp \<in> set tps" for tp
      unfolding TM_config.simps using that by blast
    show "\<forall>tp\<in>set (tapes (C ?c)). set_of_tape tp \<subseteq> symbols natM"
    proof (intro ballI)
      fix tp
      assume "tp \<in> set (tapes (C ?c))"
      then have "tp \<in> tape_map g ` set tps" unfolding cc_simps TM_config.simps set_map .
      then obtain tp' where tp': "tp = tape_map g tp'" and "tp' \<in> set tps" by blast

      have "set_of_tape tp = g ` set_of_tape tp'"
        unfolding \<open>tp = tape_map g tp'\<close> tape_set_app[of g, OF g_Bk] ..
      also have "... \<subseteq> g ` symbols M" using \<open>tp' \<in> set tps\<close> by (intro image_mono) (fact wf_tp)
      finally show "set_of_tape tp \<subseteq> symbols natM" unfolding natM_simps .
    qed
  qed
qed

lemma natM_step_eq: "wf_config c \<Longrightarrow> C\<inverse> (natM.step (C c)) = step c"
proof (induction c)
  case (fields q tps)
  let ?c = "\<lparr>state = q, tapes = tps\<rparr>" let ?c' = "C ?c"
  let ?q = "f q" and ?tps = "map (tape_map g) tps"
  let ?w = "map head tps"

  from \<open>wf_config ?c\<close> have "pre_natM.wf_config (C ?c)" by (fact wf_natM_config)
  from \<open>wf_config ?c\<close> have "q \<in> states M" using wf_configD(1)[of ?c] by simp
  with f_inv have ff_q: "f_inv (f q) = q" .
  from \<open>wf_config ?c\<close> have wf_ns: "next_state M q ?w \<in> states M"
    using wf_config_state[of ?c] by (intro next_state) simp
  from \<open>wf_config ?c\<close> have wf_step: "wf_config (step ?c)" by (fact wf_config_step)

  have tp_read_eq: "map (\<lambda>tp. g_inv (head (tape_map g tp))) tps = map head tps"
  proof (intro list.map_cong0)
    fix tp assume "tp \<in> set tps"
    with \<open>wf_config ?c\<close> have "set_of_tape tp \<subseteq> symbols M" by (fast dest: wf_config_simpD(3))
    then have "head tp \<in> symbols M" by force
    then show "g_inv (head (tape_map g tp)) = head tp"
      by (induction tp) (simp add: g_inv)
  qed

  have "state (natM.step ?c') = next_state M\<^sub>\<nat> ?q (map head ?tps)"
    unfolding natM.step_def Let_def cc_simps TM_config.simps ..
  also have "... = f (next_state M q ?w)"
    unfolding natM_def TM.TM.simps map_map unfolding ff_q comp_def tp_read_eq ..
  finally have state_step: "state (natM.step ?c') = f (next_state M q ?w)" .

  have tp_upd: "tp_update (action_app g a) (tape_map g tp) = tape_map g (tp_update a tp)" for a tp
  proof (induction tp)
    case (fields ls m rs) thus ?case
    proof (induction a)
      case L thus ?case by (induction ls) auto next
      case Shift_Right thus ?case by (induction rs) auto
    qed (* cases "(W \<sigma>)" and "Nop" by *) auto
  qed

  let ?na = "next_action M q ?w"
  have "tapes (natM.step ?c') = map2 tp_update (next_action M\<^sub>\<nat> ?q (map head ?tps)) ?tps"
    unfolding natM.step_def Let_def cc_simps TM_config.simps ..
  also have "... = map2 tp_update (map (action_app g) ?na) ?tps"
    unfolding natM_def TM.TM.simps map_map comp_def tp_read_eq ff_q ..
  also have "... = map (tape_map g) (map2 tp_update ?na tps)"
    unfolding zip_map2 map_map zip_map1 unfolding comp_def case_prod_beta' fst_conv snd_conv
    unfolding tp_upd ..
  finally have "tapes (natM.step ?c') = map (tape_map g) (map2 tp_update ?na tps)" .

  with state_step have natM_step: "natM.step ?c' = \<lparr>
    state = f (next_state M q ?w),
    tapes = map (tape_map g) (map2 tp_update ?na tps)
  \<rparr>" using unit_eq by (intro TM_config.equality) (unfold TM_config.simps)

  have "C\<inverse> (natM.step (C ?c)) = CC (step ?c)"  unfolding natM_step step_def Let_def TM_config.simps
    unfolding config_conv.simps ..
  then show "C\<inverse> (natM.step (C ?c)) = step ?c" unfolding config_conv_inv[OF wf_step] .
qed

lemma natM_steps_eq:
  "wf_config c \<Longrightarrow> C\<inverse> ((natM.step ^^ n) (C c)) = (step ^^ n) c"
proof (induction n)
  case 0 thus ?case unfolding funpow_0 by (fact config_conv_inv)
next
  case (Suc n)
  then have IH: "C\<inverse> ((natM.step ^^ n) (C c)) = (step ^^ n) c" .

  from \<open>wf_config c\<close> have wf: "wf_config ((step ^^ n) c)" by (fact wf_config_steps)
  from \<open>wf_config c\<close> have "pre_natM.wf_config (C c)" by (fact wf_natM_config)
  then have wf': "pre_natM.wf_config ((natM.step ^^ n) (C c))" by (fact natM.wf_config_steps)

  have "C\<inverse> ((natM.step ^^ Suc n) (C c)) = C\<inverse> (natM.step ((natM.step ^^ n) (C c)))"
    unfolding funpow.simps comp_def ..
  also have "... = C\<inverse> (natM.step (CC\<inverse> ((natM.step ^^ n) (C c))))"
    unfolding config_conv_inv'[OF wf'] ..
  also have "... = (step ^^ Suc n) c" unfolding IH natM_step_eq[OF wf] by simp
  finally show ?case .
qed

lemma natM_initial_config:
  shows "C (initial_config w) = natM.initial_config (map g w)"
unfolding initial_config_def natM.initial_config_def cc_simps
    unfolding list.map map_replicate tape_map.simps g_Bk
    unfolding natM_def TM.TM.simps input_tape_map[of g, OF g_Bk] ..

lemma c_inv_state: "state (C\<inverse> c) = f_inv (state c)" for c
  by (induction c) simp

lemma natM_state_eq:
  assumes "wf_word w"
  shows "state (natM.run n (map g w)) = f (state (run n w))"
proof -
  from assms have wfc: "wf_config (initial_config w)" by (rule wf_initial_config)
  hence "C\<inverse> (natM.run n (map g w)) = run n w"
    using natM_initial_config natM_steps_eq by metis
  thus ?thesis using c_inv_state
    by (metis assms inv_f natM.wf_config_run natM_wf_word pre_natM.wf_configD(1))
qed

lemma final_eq:
  assumes "wf_word w"
  shows "is_final (run n w) \<longleftrightarrow> natM.is_final (natM.run n (map g w))"
proof - (* using natM_state_eq[OF assms] try *)
  let ?w = "map g w" and ?c0 = "initial_config w"
  from \<open>wf_word w\<close> have wf_c0: "wf_config ?c0" by (fact wf_initial_config)

  have "state ((step ^^ n) ?c0) = state (C\<inverse> ((natM.step ^^ n) (C ?c0)))"
    unfolding natM_steps_eq[OF wf_c0] ..
  also have "... = f_inv (state ((natM.step ^^ n) (C ?c0)))" unfolding c_inv_state ..
  also have "... = f_inv (state (natM.run n ?w))" unfolding natM_initial_config ..
  finally have run_eq: "state (run n w) = f_inv (state (natM.run n ?w))" .

  have "pre_natM.wf_config (natM.initial_config (map g w))"
    using wf_natM_config[of ?c0] and wf_c0 unfolding natM_initial_config[symmetric] .
  then have "pre_natM.wf_config (natM.run n ?w)" by (fact natM.wf_config_steps)
  then have wf_run_state: "state (natM.run n ?w) \<in> states natM" by blast
  then have wf_run_state': "f_inv (state (natM.run n ?w)) \<in> states M" by (fact f_inv_states)

  let ?H = "final_states M"
  have H: "final_states natM = f ` ?H" unfolding natM_def TM.TM.simps ..
  have run_state_eq: "state (run n w) \<in> ?H \<longleftrightarrow> f_inv (state (natM.run n ?w)) \<in> ?H"
    unfolding run_eq ..
  also have "... \<longleftrightarrow> f (f_inv (state (natM.run n ?w))) \<in> f ` ?H"
    using f_inj wf_run_state' state_axioms(3) by (fact inj_on_image_mem_iff[symmetric])
  also have "... \<longleftrightarrow> state (natM.run n ?w) \<in> f ` ?H" unfolding inv_f[OF wf_run_state] ..
  finally show "is_final (run n w) \<longleftrightarrow> natM.is_final (natM.run n ?w)" unfolding H .
qed

lemma natM_halts': "wf_word w \<Longrightarrow> halts w \<longleftrightarrow> natM.halts (map g w)"
  unfolding halts_altdef natM.halts_altdef using final_eq natM_wf_word by presburger

lemma natM_halts: "halts w \<Longrightarrow> natM.halts (map g w)"
  unfolding halts_altdef using natM_halts' by blast

lemma natM_accepts: "accepts w \<Longrightarrow> natM.accepts (map g w)"
proof -
  assume acc: "accepts w"
  hence wwf: "wf_word w" unfolding accepts_def ..
  hence C1: "pre_natM.wf_word (map g w)" by auto

  from acc obtain n where "state (run n w) \<in> accepting_states M" by blast
  with natM_state_eq[OF wwf, of n] have C2: "\<exists>n. state (natM.run n (map g w)) \<in> accepting_states natM"
    using natM_simps(4) by force

  from C1 C2 show ?thesis using natM.acceptsI by blast
qed

lemma natM_rejects: "rejects w \<Longrightarrow> natM.rejects (map g w)"
proof -
  assume rej: "rejects w"
  hence wwf: "wf_word w" unfolding rejects_def ..
  hence C1: "pre_natM.wf_word (map g w)" by auto

  from rej obtain n where "is_final (run n w)" and "state (run n w) \<in> rejecting_states M" by blast
  with natM_state_eq[OF wwf, of n]
  have C2: "\<exists>n. state (natM.run n (map g w)) \<in> rejecting_states natM"
    using natM_rejecting_states by force

  from C1 C2 show ?thesis using natM.rejectsI by auto
qed

lemma natM_halts_all:
  assumes "\<forall>w\<in>wf_words. halts w"
    shows "\<forall>natw\<in>pre_natM.wf_words. natM.halts natw"
proof
  fix natw assume "natw \<in> pre_natM.wf_words"
  with map_g_bij obtain w where natw: "(map g) w = natw" and wwf: "w \<in> wf_words"
    using bij_betw_obtain_preimage by force
  from assms wwf have "halts w" ..
  with natM_halts have "natM.halts (map g w)" .
  thus "natM.halts natw" unfolding natw .
qed

lemma lemmy:
  assumes "wf_lang L" and "w \<in> wf_words"
      and "map g w \<in> map g ` L"
  shows "w \<in> L"
proof -
  from assms(3) obtain w' where "w'\<in>L" and "map g w = map g w'" by blast
  with assms(1-2) map_g_inj have "w = w'"
    unfolding inj_on_def by blast
  with \<open>w'\<in>L\<close> show "w \<in> L" by simp
qed

lemma rudy:
  assumes "w \<in> wf_words" and "halts w"
    and "natM.accepts (map g w)"
  shows "accepts w"
proof (rule ccontr)
  assume "\<not> accepts w"
  with \<open>halts w\<close> have "rejects w" by blast
  hence "natM.rejects (map g w)" by (rule natM_rejects)
  with natM.acc_not_rej assms(3) show "False" by blast
qed

lemma natM_decides:
  assumes dec: "decides L"
  shows "natM.decides (map g ` L)"
  unfolding natM.decides_altdef
proof
  from dec have Lwf: "wf_lang L" ..
  show "pre_natM.wf_lang (map g ` L)" proof
    fix w assume "w \<in> map g ` L"
    then obtain w' where "w'\<in>L" and "w = map g w'" by blast
    with Lwf show "w \<in> pre_natM.wf_words" by auto
  qed

  {
  fix w assume wwf: "w \<in> pre_natM.wf_words"

  let ?w' = "map g_inv w"
  from wwf g_inv_word_wf have w'wf: "?w' \<in> wf_words" by blast
  from wwf map_g_g_inv have w'inv: "map g ?w' = w" by blast
  from wwf map_g_g_inv have winv: "map g (map g_inv w) = w" by blast

  from dec natM_halts_all have "\<forall>w\<in>pre_natM.wf_words. natM.halts w"
    unfolding decides_altdef by simp
  with wwf have C1: "natM.halts w" by simp

  have C2: "(w \<in> map g ` L) \<longleftrightarrow> natM.accepts w" proof -
  have "(w \<in> map g ` L) \<longleftrightarrow> ?w' \<in> L" proof
      assume "w \<in> map g ` L"
      with lemmy[OF Lwf, OF w'wf] w'inv show "?w' \<in> L" by blast
    next
      assume "map g_inv w \<in> L"
      hence "map g (map g_inv w) \<in> map g ` L" by blast
      then show "w \<in> map g ` L" unfolding winv .
  qed
  also have "map g_inv w \<in> L \<longleftrightarrow> accepts ?w'"
    using dec decides_altdef w'wf by simp
  also have "accepts ?w' \<longleftrightarrow> natM.accepts w"
    using natM_accepts rudy C1
    by (metis dec decides_altdef w'wf winv)
  finally show ?thesis .
  qed
  from C1 C2 have "natM.halts w \<and> (w \<in> map g ` L) = natM.accepts w" ..
  }
  thus "\<forall>w\<in>{w. set w \<subseteq> symbols M\<^sub>\<nat>}. natM.halts w \<and> (w \<in> map g ` L) = natM.accepts w" ..
qed

end \<comment> \<open>\<^locale>\<open>nat_TM\<close>\<close>

typedef (overloaded) ('q, 's) wf_TM = "{M::('q, 's) TM. TM M}"
  using exists_wf_TM by blast

end
