theory TM
  imports Main
begin

class blank =
  fixes B :: 'a

datatype 'b action = L | R | W (symbol_of_write: 'b)

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

fun tp_read :: "('b :: blank) tape \<Rightarrow> 'b" where
  "tp_read \<lparr>left=_, right=[]  \<rparr> = B"
| "tp_read \<lparr>left=_, right=r#rs\<rparr> = r"

record ('a, 'b) TM =
  k :: nat (*number of tapes*)

  states       :: "'a set"
  start_state  :: 'a
  final_states :: "'a set"

  symbols :: "'b set"
    
  next_state  :: "'a \<Rightarrow> 'b list \<Rightarrow> 'a"
  next_action :: "'a \<Rightarrow> 'b list \<Rightarrow> 'b action list"

record ('a, 'b) TM_config =
  state :: 'a
  tapes  :: "'b tape list"

locale wf_TM =
  fixes M :: "('a, 'b::blank) TM" (structure)
  assumes "1 \<le> k M"
  and "finite (states M)" "start_state M \<in> states M" "final_states M \<subseteq> states M"
  and "finite (symbols M)" "B \<in> (symbols M)"
  and "\<forall>q\<in>states M. \<forall>w. length w = k M \<longrightarrow> set w \<subseteq> symbols M \<longrightarrow>
       next_state M q w \<in> states M
     \<and> length (next_action M q w) = k M
     \<and> symbol_of_write ` set (next_action M q w) \<subseteq> symbols M"
  and finalNextFinal: "\<forall>q\<in>final_states M. \<forall>w. next_state M q w \<in> final_states M"
begin
definition is_final :: "('a, 'b) TM_config \<Rightarrow> bool" where
  "is_final c \<longleftrightarrow> state c \<in> final_states M"

definition step :: "('a, 'b) TM_config \<Rightarrow> ('a, 'b) TM_config" where
  "step c = (let q=state c; w=map tp_read (tapes c) in \<lparr>
      state=next_state M q w,
      tapes=map2 tp_update (next_action M q w) (tapes c)
   \<rparr>)"

lemma finalFinal: "is_final c \<Longrightarrow> is_final (step c)"
  unfolding is_final_def step_def using finalNextFinal
  by (metis TM_config.select_convs(1))

definition start_config :: "'b list \<Rightarrow> ('a, 'b) TM_config" where
  "start_config w = \<lparr>
    state = start_state M,
    tapes = <w>\<^sub>t\<^sub>p # replicate (k M - 1) empty_tape
  \<rparr>"

end \<comment> \<open>\<^locale>\<open>wf_TM\<close>\<close>

locale acceptor = wf_TM +
  fixes accepting_states :: "'a set"
  assumes "accepting_states \<subseteq> states M"
begin
end

end