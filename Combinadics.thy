theory Combinadics
  imports "HOL.Binomial" Binary
begin

(* https://en.wikipedia.org/wiki/Combinatorial_number_system *)

definition nat_of_set :: "nat set \<Rightarrow> nat" where
  "nat_of_set S = (\<Sum>x\<in>S. 2^x)"

fun set_of_bin :: "bin \<Rightarrow> nat \<Rightarrow> nat set" where
 "set_of_bin [] _ = {}"
|"set_of_bin (True#xs) n = insert n (set_of_bin xs (Suc n))"
|"set_of_bin (False#xs) n = set_of_bin xs (Suc n)"

definition set_of_nat :: "nat \<Rightarrow> nat set" where
  "set_of_nat n = set_of_bin (bin_of_nat n) 0"


lemma "infinite S \<Longrightarrow> nat_of_set S = 0" unfolding nat_of_set_def by simp

lemma "nat_of_set (set_of_nat n) = n"
  sorry

lemma nat_of_set_inv: "finite S \<Longrightarrow> set_of_nat (nat_of_set S) = S"
  sorry

lemma nat_of_set_inj:
  assumes "finite A" "finite B"
    and "nat_of_set A = nat_of_set B"
  shows "A = B"
proof -
  from \<open>nat_of_set A = nat_of_set B\<close>
  have "set_of_nat (nat_of_set A) = set_of_nat (nat_of_set B)" by (rule arg_cong)
  thus "A = B" using assms(1-2) by (subst (asm) (1 2) nat_of_set_inv) auto
qed

definition less_eq_lex where
  "less_eq_lex A B \<longleftrightarrow> nat_of_set A \<le> nat_of_set B"

definition less_lex where
  "less_lex A B \<longleftrightarrow> nat_of_set A < nat_of_set B"

interpretation natset_lex_ord:
  linorder less_eq_lex less_lex
  apply standard
  apply (auto simp add: less_eq_lex_def less_lex_def)
  sorry (* inconsistent for infinite sets? *)
(* how to define an linorder for finite nat sets only? *)

definition nat_of_combination :: "nat set \<Rightarrow> nat" where
  "nat_of_combination X = card {Y. card Y = card X \<and> less_lex Y X}"

definition combination_of_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "combination_of_nat k n = (THE S. card S = k \<and> nat_of_combination S = n)"

lemma "0 < k \<Longrightarrow> nat_of_combination (combination_of_nat k n) = n"
  sorry

lemma "finite S \<Longrightarrow> combination_of_nat (card S) (nat_of_combination S) = S"
  sorry

definition subset_sfx :: "nat set \<Rightarrow> nat set \<Rightarrow> bool" where
  "subset_sfx P X \<longleftrightarrow> P\<subseteq>X \<and> (\<forall>x\<in>X. x\<in>P \<or> (\<forall>p\<in>P. x \<le> p))"

lemma subset_sfx_altdef:
  "subset_sfx P X \<longleftrightarrow> P\<subseteq>X \<and> suffix (sorted_list_of_set P) (sorted_list_of_set X)"
  sorry

lemma finite_sfx_max: 
  assumes "subset_sfx P X" "finite P" "P\<noteq>{}"
  obtains m where "m\<in>P" and "\<forall>x\<in>X. x \<le> m"
proof -
  from \<open>finite P\<close> \<open>P\<noteq>{}\<close>
  obtain m where *: "\<forall>p\<in>P. p \<le> m" and "m\<in>P"
    using Max_eq_iff by blast
  have "\<forall>x\<in>X. x \<le> m" proof
    fix x assume "x\<in>X"
    thus "x \<le> m" proof (cases "x \<in> P")
      case False
      with \<open>subset_sfx P X\<close> \<open>x\<in>X\<close> \<open>m\<in>P\<close>
      show ?thesis unfolding subset_sfx_def by blast
    qed (simp add: *)
  qed
  with that \<open>m\<in>P\<close> show thesis .
qed

corollary
  assumes "subset_sfx {m} X"
  shows "Max X = m"
proof (subst Max_eq_iff)
  have *: "\<forall>x\<in>X. x \<le> m"
    using assms finite_sfx_max by blast
  from * show "finite X"
    unfolding finite_nat_set_iff_bounded_le ..
  from assms have "m\<in>X"
    unfolding subset_sfx_def by blast
  thus "X\<noteq>{}" by blast
  from \<open>m\<in>X\<close> * show "m \<in> X \<and> (\<forall>a\<in>X. a \<le> m)" ..
qed 

lemma
  fixes X::"nat set"
  shows "card {Y. Max Y = Max X \<and> card Y = card X \<and> less_eq_lex Y X} = (Max X choose (card X - 1))"
sorry

theorem nat_of_combination_altdef:
"nat_of_combination X = (let cs = enumerate 1 (sorted_list_of_set X) in
              fold (\<lambda>(i, c) acc. acc + (c choose i)) cs 0)"
  sorry

end