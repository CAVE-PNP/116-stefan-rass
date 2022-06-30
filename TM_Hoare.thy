subsection \<open>Hoare Rules\<close>

theory TM_Hoare
  imports Computability
begin


type_synonym ('q, 's) assert = "('q, 's) TM_config \<Rightarrow> bool"

definition hoare_halt :: "('q, 's) assert \<Rightarrow> ('q, 's) TM \<Rightarrow> ('q, 's) assert \<Rightarrow> bool"
  where "hoare_halt P M Q \<equiv>
    (\<forall>c. P c \<longrightarrow> (\<exists>n. let cn = TM.steps M n c in TM.is_final M cn \<and> Q cn))"

lemma hoare_haltI[intro]:
  fixes P Q
  assumes "\<And>c. P c \<Longrightarrow> \<exists>n. TM.is_final M (TM.steps M n c) \<and> Q (TM.steps M n c)"
  shows "hoare_halt P M Q"
  unfolding hoare_halt_def Let_def using assms by blast

lemma hoare_haltE[elim]:
  fixes c
  assumes "hoare_halt P M Q"
    and "P c"
  obtains n where "TM.is_final M (TM.steps M n c)" and "Q (TM.steps M n c)"
  using assms
  unfolding hoare_halt_def Let_def by blast

lemma hoare_haltE2[elim]:
  fixes c
  assumes "hoare_halt P M Q"
    and "P c"
  shows "\<exists>n. TM.is_final M (TM.steps M n c) \<and> Q (TM.steps M n c)"
  using assms unfolding hoare_halt_def Let_def by blast

lemma hoare_contr:
  assumes "hoare_halt P M (\<lambda>_. False)" and "P c"
  shows "False"
  using assms by (rule hoare_haltE)

lemma hoare_imp[elim]:
  assumes "hoare_halt P M Q"
    and P': "\<And>c. P' c \<Longrightarrow> P c"
    and Q': "\<And>c. Q c \<Longrightarrow> Q' c"
  shows "hoare_halt P' M Q'"
proof (intro hoare_haltI)
  fix c assume "P' c"
  with P' and \<open>hoare_halt P M Q\<close> obtain n
    where f: "TM.is_final M (TM.steps M n c)" and Q: "Q (TM.steps M n c)" by blast
  with Q' show "\<exists>n. TM.is_final M (TM.steps M n c) \<and> Q' (TM.steps M n c)" by blast
qed


lemma hoare_true: "hoare_halt P M Q \<Longrightarrow> hoare_halt P M (\<lambda>_. True)" by fast

lemma hoare_and[intro]:
  assumes h1: "hoare_halt P M Q1"
    and h2: "hoare_halt P M Q2"
  shows "hoare_halt P M (\<lambda>c. Q1 c \<and> Q2 c)"
proof
  fix c assume "P c"
  from h1 and \<open>P c\<close> obtain n1
    where fn1: "TM.is_final M (TM.steps M n1 c)" and q1: "Q1 (TM.steps M n1 c)" by (rule hoare_haltE)
  from h2 and \<open>P c\<close> obtain n2
    where fn2: "TM.is_final M (TM.steps M n2 c)" and q2: "Q2 (TM.steps M n2 c)" by (rule hoare_haltE)

  define n::nat where "n \<equiv> max n1 n2"
  hence "n1 \<le> n" "n2 \<le> n" by simp+
  let ?cn = "TM.steps M n c"
  from fn1 and \<open>n1 \<le> n\<close> have steps1: "?cn = TM.steps M n1 c" by (fact TM.final_le_steps)
  from fn2 and \<open>n2 \<le> n\<close> have steps2: "?cn = TM.steps M n2 c" by (fact TM.final_le_steps)
  from fn1 q1 q2 have "TM.is_final M ?cn \<and> Q1 ?cn \<and> Q2 ?cn" by (fold steps1 steps2) blast
  then show "\<exists>n. TM.is_final M (TM.steps M n c) \<and> Q1 (TM.steps M n c) \<and> Q2 (TM.steps M n c)" ..
qed


lemma halts_config_altdef: "TM.halts_config M c \<longleftrightarrow> hoare_halt (\<lambda>x. x = c) M (\<lambda>_. True)"
  unfolding TM.halts_config_def by fast

lemma (in TM) hoare_halt_init_conf:
  "hoare_halt (TM.on_input M w) M P \<longleftrightarrow> (\<exists>n. let cn = run n w in is_final cn \<and> P cn)"
  unfolding hoare_halt_def TM.on_input_def run_def by blast

lemma halts_altdef: "TM.halts M w \<longleftrightarrow> hoare_halt (TM.on_input M w) M (\<lambda>_. True)"
  unfolding TM.halts_def halts_config_altdef TM.on_input_def ..

lemma hoare_halt_neg:
  assumes "\<not> hoare_halt (TM.on_input M w) M Q"
    and "TM.halts M w"
  shows "hoare_halt (TM.on_input M w) M (\<lambda>tp. \<not> Q tp)"
  using assms unfolding hoare_halt_def TM.halts_def Let_def TM.on_input_def by fast


lemma halt_inj:
  assumes "hoare_halt (TM.on_input M w) M (\<lambda>c. f c = x)"
      and "hoare_halt (TM.on_input M w) M (\<lambda>c. f c = y)"
    shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  then have *: "a = x \<and> a = y \<longleftrightarrow> False" for a by blast

  from assms have "hoare_halt (TM.on_input M w) M (\<lambda>c. f c = x \<and> f c = y)" by (rule hoare_and)
  then have "hoare_halt (TM.on_input M w) M (\<lambda>_. False)" unfolding * .
  then show False by blast
qed


subsubsection\<open>Computes Predicate\<close>

context TM
begin

(* TODO document, clean up *)

definition (in -) [simp]: "hoare_run w M P \<equiv> hoare_halt (TM.on_input M w) M P"

definition "computes_word w w' \<equiv> hoare_run w M (\<lambda>c. clean_output c \<and> output_of c = w')"


lemma hoare_run_altdef: "hoare_run w M P \<longleftrightarrow> halts w \<and> P (compute w)"
proof (rule iffI)
  assume "hoare_run w M P"
  then have "\<exists>n. let cn = run n w in is_final cn \<and> P cn"
    unfolding hoare_run_def hoare_halt_init_conf .
  then obtain n where "is_final (run n w)" and "P (run n w)" unfolding Let_def by blast
  then show "halts w \<and> P (compute w)" using computeI by blast
next
  assume "halts w \<and> P (compute w)"
  then have "halts w" and "P (compute w)" by blast+
  from \<open>halts w\<close> have "is_final (compute w)" by blast
  with \<open>P (compute w)\<close> show "hoare_run w M P"
    unfolding hoare_run_def hoare_halt_init_conf Let_def by blast
qed


definition "computes f \<equiv> \<forall>w. computes_word w (f w)"
declare (in -) TM.computes_def[simp]

lemma hoare_run_halts[dest]: "hoare_run w M P \<Longrightarrow> halts w"
  unfolding halts_altdef hoare_run_def by (rule hoare_true)

lemma computes_word_halts[dest]: "computes_word w w' \<Longrightarrow> halts w"
  unfolding computes_word_def by (rule hoare_run_halts)

lemma computes_halts[dest]: "computes f \<Longrightarrow> halts w"
  unfolding halts_altdef2 by auto


lemma hoare_run_run[dest]: "hoare_run w M P \<Longrightarrow> P (compute w)" unfolding hoare_run_altdef by blast

lemma run_hoare_run[simp]: "halts w \<Longrightarrow> hoare_run w M P = P (compute w)"
  unfolding hoare_run_altdef by blast


lemma computes_word_output[dest]:
  assumes "computes_word w w'"
  shows "last (tapes (compute w)) = <w'>\<^sub>t\<^sub>p"
proof -
  let ?c = "run (time w) w"
  from assms have "clean_output ?c" and "output_of ?c = w'" unfolding computes_word_def by blast+
  then obtain x where "last (tapes ?c) = <x>\<^sub>t\<^sub>p" unfolding clean_output_def by blast
  then have "output_of ?c = x" by blast
  with \<open>output_of ?c = w'\<close> have "x = w'" by blast
  with \<open>last (tapes ?c) = <x>\<^sub>t\<^sub>p\<close> show ?thesis by blast
qed

lemma computes_output: "computes f \<Longrightarrow> last (tapes (compute w)) = <f w>\<^sub>t\<^sub>p"
  by (intro computes_word_output) simp

lemma output_computes_word:
  assumes "halts w"
    and "last (tapes (compute w)) = <w'>\<^sub>t\<^sub>p"
  shows "computes_word w w'"
  unfolding computes_word_def run_hoare_run[OF \<open>halts w\<close>] clean_output_alt by (fact assms(2))


lemma computes_word_altdef: "computes_word w w' \<longleftrightarrow> halts w \<and> last (tapes (compute w)) = <w'>\<^sub>t\<^sub>p"
  unfolding computes_word_def hoare_run_altdef by blast

end \<comment> \<open>context \<^locale>\<open>TM\<close>\<close>

end
