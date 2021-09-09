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

theorem nat_of_combination_altdef:
"nat_of_combination X = (let cs = enumerate 1 (sorted_list_of_set X) in
              fold (\<lambda>(i, c) acc. acc + (c choose i)) cs 0)"
  sorry

end