theory ex4_1
  imports Main
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

lemma contradiction_example_auto: 
  fixes x y A T
  assumes "\<forall>x y. T x y \<or> T y x"
    and "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
    and "\<forall>x y. T x y \<longrightarrow> A x y" 
    and "A x y"
  shows "T x y"
  using assms by blast
