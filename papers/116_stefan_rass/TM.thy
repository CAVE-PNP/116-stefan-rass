theory TM
  imports Main "Supplementary/Misc"
begin

class blank =
  fixes B :: 'a

instantiation nat :: blank begin
  definition B_nat :: nat where "B_nat = 0"
  instance ..
end

datatype 'b action = L | R | W 'b | Nop

fun symbol_of_write :: "'b action \<Rightarrow> 'b::blank" where
  "symbol_of_write (W w) = w" | "symbol_of_write _ = B"

record 'b tape =
  left :: "'b list"
  right :: "'b list"

abbreviation "empty_tape \<equiv> \<lparr>left=[], right=[]\<rparr>"

text\<open>TM execution begins with the head at the start of the input word.\<close>
abbreviation input_tape ("<_>\<^sub>t\<^sub>p") where "<w>\<^sub>t\<^sub>p \<equiv> \<lparr>left=[], right=w\<rparr>"

abbreviation size :: "'b tape \<Rightarrow> nat" where
  "size tp \<equiv> length (left tp) + length (right tp)"

fun tp_update :: "('b::blank) action \<Rightarrow> 'b tape \<Rightarrow> 'b tape" where
 "tp_update  L     \<lparr>left=[]  , right=rs  \<rparr> = \<lparr>left=[]  , right=B#rs\<rparr>"
|"tp_update  L     \<lparr>left=l#ls, right=rs  \<rparr> = \<lparr>left=ls  , right=l#rs\<rparr>"
|"tp_update  R     \<lparr>left=ls  , right=[]  \<rparr> = \<lparr>left=B#ls, right=[]  \<rparr>"
|"tp_update  R     \<lparr>left=ls  , right=r#rs\<rparr> = \<lparr>left=r#ls, right=rs  \<rparr>"
|"tp_update (W w)  \<lparr>left=ls  , right=[]  \<rparr> = \<lparr>left=ls  , right=[w] \<rparr>"
|"tp_update (W w)  \<lparr>left=ls  , right=r#rs\<rparr> = \<lparr>left=ls  , right=w#rs\<rparr>"
|"tp_update Nop tape = tape"

fun tp_read :: "('b :: blank) tape \<Rightarrow> 'b" where
  "tp_read \<lparr>left=_, right=[]  \<rparr> = B"
| "tp_read \<lparr>left=_, right=r#rs\<rparr> = r"

record ('a, 'b) TM =
  tape_count :: nat

  states       :: "'a set"
  start_state  :: 'a
  final_states :: "'a set"
  accepting_states :: "'a set"

  symbols :: "'b set"
    
  next_state  :: "'a \<Rightarrow> 'b list \<Rightarrow> 'a"
  next_action :: "'a \<Rightarrow> 'b list \<Rightarrow> 'b action list"

record ('a, 'b) TM_config =
  state :: 'a
  tapes  :: "'b tape list"

locale wf_TM =
  fixes M :: "('a, 'b::blank) TM" (structure)
  assumes "1 \<le> tape_count M"
  and "finite (states M)" "start_state M \<in> states M" "final_states M \<subseteq> states M"
  and "accepting_states M \<subseteq> final_states M"
  and "finite (symbols M)" "B \<in> (symbols M)"
  and "\<forall>q\<in>states M. \<forall>w. length w = tape_count M \<longrightarrow> set w \<subseteq> symbols M \<longrightarrow>
       next_state M q w \<in> states M
     \<and> length (next_action M q w) = tape_count M
     \<and> symbol_of_write ` set (next_action M q w) \<subseteq> symbols M"
  and final_state: "\<forall>q\<in>final_states M. \<forall>w. next_state M q w = q"
  and final_action: "\<forall>q\<in>final_states M. \<forall>w. set (next_action M q w) \<subseteq> {Nop}"
begin
definition is_final :: "('a, 'b) TM_config \<Rightarrow> bool" where
  "is_final c \<longleftrightarrow> state c \<in> final_states M"

definition step :: "('a, 'b) TM_config \<Rightarrow> ('a, 'b) TM_config" where
  "step c = (let q=state c; w=map tp_read (tapes c) in \<lparr>
      state=next_state M q w,
      tapes=map2 tp_update (next_action M q w) (tapes c)
   \<rparr>)"

lemma final_step_fixpoint: "is_final c \<Longrightarrow> step c = c"
  sorry

lemma final_steps: "\<And>n. is_final c \<Longrightarrow> (step^^n) c = c"
  using final_step_fixpoint[of c] funpow_fixpoint by metis

definition start_config :: "'b list \<Rightarrow> ('a, 'b) TM_config" where
  "start_config w = \<lparr>
    state = start_state M,
    tapes = <w>\<^sub>t\<^sub>p # replicate (tape_count M - 1) empty_tape
  \<rparr>"

abbreviation "run n w \<equiv> (step^^n) (start_config w)"

lemma final_le_steps:
  assumes "is_final ((step^^n) c)"
      and "n \<le> m"
    shows "(step^^m) c = (step^^n) c"
proof -
  from \<open>n\<le>m\<close> obtain n' where "m = n' + n"
    by (metis add.commute less_eqE)
  then have "(step^^m) c = (step^^n') ((step^^n) c)"
    using funpow_add[of n' n step] by simp
  thus "(step^^m) c = (step^^n) c"
    using final_steps[of "(step^^n) c" n'] assms(1) by simp
qed

end \<comment> \<open>\<^locale>\<open>wf_TM\<close>\<close>

subsection \<open>Composition of Turing Machines\<close>

fun tm_comp :: "('a1, 'b::blank) TM \<Rightarrow> ('a2, 'b) TM \<Rightarrow> ('a1+'a2, 'b) TM" ("_ |+| _" [0, 0] 100)
  where "tm_comp M1 M2 = \<lparr>
    tape_count = max (tape_count M1) (tape_count M2),
    states = states M1 <+> states M2,
    start_state = Inl (start_state M1),
    final_states = Inr`final_states M2,
    accepting_states = Inr`accepting_states M2,
    symbols = symbols M1 \<union> symbols M2,
    next_state = (\<lambda>q w. q),
    next_action = (\<lambda>q w. [W B])
  \<rparr>" (*TODO!*)

lemma "wf_TM M1 \<Longrightarrow> wf_TM M2 \<Longrightarrow> wf_TM (M1 |+| M2)"
  sorry

subsection \<open>Hoare Rules\<close>

type_synonym ('a, 'b) assert = "('a, 'b) TM_config \<Rightarrow> bool"

definition (in wf_TM) hoare_halt :: "('a, 'b) assert \<Rightarrow> ('a, 'b) assert \<Rightarrow> bool" where
  "hoare_halt P Q \<longleftrightarrow> (\<forall>c. P c \<longrightarrow>
    (\<exists>n. let cn = (step^^n) c in is_final cn \<and> Q cn))"

lemma (in wf_TM) hoare_haltI[intro]:
  fixes P Q
  assumes "\<And>c. P c \<Longrightarrow>
             \<exists>n. let cn = (step^^n) c in is_final cn \<and> Q cn"
  shows "hoare_halt P Q"
  unfolding hoare_halt_def using assms by blast

(* lemma (in wf_TM) hoare_haltI[intro]:
  fixes P Q n
  assumes "\<And>c. P c \<Longrightarrow> is_final ((step^^n) c)"
  assumes "\<And>c. P c \<Longrightarrow> Q ((step^^n) c)"
  shows "hoare_halt P Q"
  unfolding hoare_halt_def Let_def using assms by blast *)

lemma (in wf_TM) hoare_haltE[elim]:
  fixes c
  assumes "P c"
      and "hoare_halt P Q"
    obtains n where "is_final ((step^^n) c)" and "Q ((step^^n) c)"
  using assms
  unfolding hoare_halt_def by meson

end