theory Threshold_Functions
  imports Main "HOL.Binomial" "HOL.Real" "HOL.Limits"
begin

definition th_prop where
  "th_prop n Q \<equiv> Collect Q \<subseteq> Pow {1..n}"

definition th_mono_inc where
  "th_mono_inc (n::nat) Q \<equiv> \<forall>B\<subseteq>{1..n}. \<forall>A\<subseteq>B. Q A \<longrightarrow> Q B"

definition th_mono_dec where
  "th_mono_dec (n::nat) Q \<equiv> (\<forall>A\<subseteq>{1..n}. \<forall>B\<subseteq>A. Q A \<longrightarrow> Q B)"

lemma th_mono_inc_dec : "th_mono_inc n Q \<longleftrightarrow> th_mono_dec n (\<lambda>A. \<not> Q A)"
  unfolding th_mono_inc_def th_mono_dec_def
  by (safe) blast+

definition th_non_triv where
  "th_non_triv (n::nat) Q \<equiv> Collect Q \<noteq> {} \<and> Collect Q \<subset> Pow {1..n}"

lemma th_non_triv_mono:
  assumes "th_prop n Q"
      and "th_mono_inc n Q"
    shows "th_non_triv n Q \<longleftrightarrow> \<not> Q {} \<and> Q {1..n}"
using assms
proof (intro iffI conjI)
  fix n Q assume assms: "th_non_triv n Q" "th_mono_inc n Q"

  show "\<not> Q {}" proof
    assume "Q {}"
    then have "\<forall>A\<subseteq>{1..n}. Q A"
      using assms unfolding th_non_triv_def th_mono_inc_def by blast
    thus False using assms(1) unfolding th_non_triv_def by blast
  qed
  
  from assms(1) obtain A where "A \<subseteq> {1..n}" and "Q A"
    unfolding th_non_triv_def by auto
  then show "Q {1..n}"
    using assms(2) unfolding th_mono_inc_def by blast
next
  fix n::nat and Q assume "\<not> Q {} \<and> Q {1..n}" "th_prop n Q"
  then show "th_non_triv n Q"
    unfolding th_non_triv_def th_prop_def by blast
qed

(* probability of a random k-subset of {1..n} having Q *)
definition th_Pk where
  "th_Pk n k Q \<equiv> card {A\<in>Pow {1..n}. card A = k \<and> Q A} / (binomial n k)"

definition th_almost_every where
  "th_almost_every k Q \<equiv> (\<lambda>n. th_Pk n (k n) Q) \<longlonglongrightarrow> 1"

definition th_almost_none where
  "th_almost_none k Q \<equiv> (\<lambda>n. th_Pk n (k n) Q) \<longlonglongrightarrow> 0"

definition th_threshold where
  "th_threshold M Q \<equiv>
    \<forall>m. let q=\<lambda>n. (m n)/of_nat (M n) in
      (q \<longlonglongrightarrow> 0) \<longrightarrow> th_almost_none m Q
    \<and> (q \<longlonglongrightarrow> 1) \<longrightarrow> th_almost_every m Q"

(*every non-trivial monotone increasing property has a threshold function *)
theorem mono_ex_th:
  assumes "th_mono_inc n Q"
      and "th_non_triv n Q"
    obtains M where "th_threshold M Q"
  sorry

(* something's fishy because mono_inc and non_triv are defined with n but th_threshold is not *)

end