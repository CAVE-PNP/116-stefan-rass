theory Threshold_Functions
  imports Main
begin

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
  assumes "th_mono_inc n Q"
      and "Collect Q \<subseteq> Pow {1..n}"
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
  fix n::nat and Q assume "\<not> Q {} \<and> Q {1..n}" "Collect Q \<subseteq> Pow {1..n}"
  then show "th_non_triv n Q" unfolding th_non_triv_def by blast
qed
  
end