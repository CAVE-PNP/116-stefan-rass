theory TM_Arith_Bin
  imports Binary "Cook_Levin.Arithmetic"
begin


lemma num_Nil[simp]: "num [] = 0" unfolding num_def by force

lemma num_altdef: "num xs = nat_of_bin (map (\<lambda>n. if n = \<one> then \<bbbI> else \<bbbO>) xs)"
  by (induction xs) (force simp: num_Cons)+

lemma canrepr_altdef[code]: "canrepr n = map (\<lambda>b. case b of \<bbbO> \<Rightarrow> \<zero> | \<bbbI> \<Rightarrow> \<one>) (bin_of_nat n)"
  (is "_ = ?rhs n")
proof (induction n rule: log2_induct')
  case (div n)
  let ?x = "?rhs n"

  show "canrepr n = ?x"
  proof (rule canreprI)
    show "canonical ?x" unfolding canonical_def
    proof (rule conjI)
      show "\<forall>i<length ?x. ?x ! i = \<zero> \<or> ?x ! i = \<one>" by (simp add: case_bool_if)
      show "?x = [] \<or> last ?x = \<one>" using bin_of_nat_last_cases
        by (rule disj_forward) (force simp: last_map)+
    qed

    have "(if (case x of \<bbbO> \<Rightarrow> \<zero> | \<bbbI> \<Rightarrow> \<one>) = 3 then \<bbbI> else \<bbbO>) = x" for x by (induction x) auto
    then show "num ?x = n" unfolding num_altdef by (simp add: comp_def)
  qed
qed (unfold canrepr_0 canrepr_1, simp_all)


end
