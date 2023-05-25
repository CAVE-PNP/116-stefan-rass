theory TM_Arith_Bin
  imports Binary "Cook_Levin.Arithmetic"
begin

abbreviation "bin_to_sym b \<equiv> case b of \<bbbO> \<Rightarrow> \<zero> | \<bbbI> \<Rightarrow> \<one>"
abbreviation "sym_to_bin z \<equiv> if z = \<one> then \<bbbI> else \<bbbO>"

lemma map_id_list_allI: "list_all (\<lambda>x. f x = x) xs \<Longrightarrow> map f xs = xs"
  unfolding list.pred_set by (intro map_idI) blast

lemma bit_symbols_altdef: "bit_symbols xs = list_all (\<lambda>z. z = \<zero> \<or> z = \<one>) xs"
   unfolding list_all_length ..

lemma sym_to_bin_to_sym[simp]: "sym_to_bin (bin_to_sym b) = b" by (induction b) auto
lemma bin_to_sym_to_bin: "z = \<zero> \<or> z = \<one> \<Longrightarrow> bin_to_sym (sym_to_bin z) = z" by fastforce
lemma map_bin_to_sym_to_bin[simp]: "bit_symbols xs \<Longrightarrow> map (bin_to_sym o sym_to_bin) xs = xs"
  unfolding comp_def bit_symbols_altdef
  by (intro map_id_list_allI, elim list.pred_mono_strong) (intro bin_to_sym_to_bin)


lemma num_Nil[simp]: "num [] = 0" unfolding num_def by force

lemma num_altdef: "num xs = nat_of_bin (map sym_to_bin xs)"
  by (induction xs) (force simp: num_Cons)+

lemma canrepr_altdef[code]: "canrepr n = map bin_to_sym (bin_of_nat n)"
  (is "_ = ?rhs n")
proof (induction n rule: log2_induct')
  case (div n)
  let ?x = "?rhs n"

  show "canrepr n = ?x"
  proof (rule canreprI)
    show "canonical ?x" unfolding canonical_def
    proof (rule conjI)
      show "bit_symbols ?x" by (simp add: case_bool_if)
      show "?x = [] \<or> last ?x = \<one>" using bin_of_nat_last_cases
        by (rule disj_forward) (force simp: last_map)+
    qed

    have "sym_to_bin (bin_to_sym x) = x" for x by (induction x) auto
    then show "num ?x = n" unfolding num_altdef by (simp add: comp_def)
  qed
qed (unfold canrepr_0 canrepr_1, simp_all)


end
