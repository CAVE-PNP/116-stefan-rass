theory ex4_1
  imports Main HOL.HOL
begin

lemma contradiction_example: 
  fixes x y A T
  assumes T: "\<forall>x y. T x y \<or> T y x"
    and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
    and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  with T have s: "T y x" by blast
  with TA have "A y x" by blast
  with `A x y` A have "x = y" by blast
  with s have "T x y" by blast
  with `\<not> T x y` show "False" by blast
qed

lemma contradiction_example_explicit: 
  fixes x y A T
  assumes T: "\<forall>x y. T x y \<or> T y x"
    and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
    and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  thm allE
  (* it seems rule is not strong enough for this goal, as there are multiple variables to specialize *)
  from T have a: "T x y \<or> T y x" by simp
  then have s: "T y x"
  proof (* "standard" this works because a disjunctive statement is piped in (via "then") *)
    assume "T x y"
    with \<open>\<not> T x y\<close> show "T y x" by (rule notE) (* by contradiction *)
  (* this part is optional, as "qed" will perform simplification automatically
  next
    assume "T y x"
    then show "T y x" .
  *)
  qed
  
  with TA have "A y x" by simp
  with \<open>A x y\<close> and A have "x = y" by simp
  with s have "T x y" by simp
  with \<open>\<not> T x y\<close> show "False" by (rule 
qed

lemma contradiction_example_auto: 
  fixes x y A T
  assumes "\<forall>x y. T x y \<or> T y x"
    and "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
    and "\<forall>x y. T x y \<longrightarrow> A x y" 
    and "A x y"
  shows "T x y"
  using assms by blast
