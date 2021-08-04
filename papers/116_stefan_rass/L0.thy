theory L0
  imports Complexity
begin


section\<open>Time Hierarchy Theorem and the Diagonal Language\<close>

locale tht_assms =
  fixes T t :: "nat \<Rightarrow> nat"
  assumes "fully_tconstr T"
    and "lim (\<lambda>l. t l * log 2 (t l) / T l) = 0"
begin


text\<open>\<open>L\<^sub>D\<close>, defined as part of the proof for the Time Hierarchy Theorem.

  "The “diagonal-language” \<open>L\<^sub>D\<close> is thus defined over the alphabet \<open>\<Sigma> = {0, 1}\<close> as
      \<open>LD := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w within \<le> T(len (w)) steps}\<close>.    (9)"\<close>

definition L\<^sub>D :: "lang"
  where LD_def[simp]: "L\<^sub>D \<equiv> {w. let M\<^sub>w = TM_decode_pad w in
                  rejects M\<^sub>w w \<and> the (time M\<^sub>w <w>\<^sub>t\<^sub>p) \<le> tcomp T (length w)}"

lemma L\<^sub>DE[elim]:
  fixes w
  assumes "w \<in> L\<^sub>D"
  defines "M\<^sub>w \<equiv> TM_decode_pad w"
  shows "rejects M\<^sub>w w"
    and "halts M\<^sub>w w"
    and "the (time M\<^sub>w <w>\<^sub>t\<^sub>p) \<le> tcomp T (length w)"
    and "\<exists>n. time M\<^sub>w <w>\<^sub>t\<^sub>p = Some n \<and> n \<le> tcomp T (length w)"
proof -
  from \<open>w \<in> L\<^sub>D\<close> show "rejects M\<^sub>w w" unfolding M\<^sub>w_def LD_def Let_def by blast
  then show "halts M\<^sub>w w" unfolding rejects_def halts_def by (rule hoare_true)

  define n where "n = the (time M\<^sub>w <w>\<^sub>t\<^sub>p)"
  from \<open>w \<in> L\<^sub>D\<close> show time_T: "the (time M\<^sub>w <w>\<^sub>t\<^sub>p) \<le> tcomp T (length w)"
    unfolding M\<^sub>w_def LD_def Let_def by blast
  then have "n \<le> tcomp T (length w)" unfolding n_def .
  moreover from \<open>halts M\<^sub>w w\<close> have "time M\<^sub>w <w>\<^sub>t\<^sub>p = Some n" unfolding n_def halts_altdef by force
  ultimately show "\<exists>n. time M\<^sub>w <w>\<^sub>t\<^sub>p = Some n \<and> n \<le> tcomp T (length w)" by blast
qed


lemma tht_h1: "DTIME t \<subseteq> DTIME T" sorry

lemma tht_h2: "L\<^sub>D \<in> DTIME T" "L\<^sub>D \<notin> DTIME t" sorry

theorem time_hierarchy: "DTIME t \<subset> DTIME T"
proof
  show "DTIME t \<subseteq> DTIME T" by (rule tht_h1)
  have "L\<^sub>D \<in> DTIME T" and "L\<^sub>D \<notin> DTIME t" by (rule tht_h2)+
  then show "DTIME t \<noteq> DTIME T" by blast
qed


section\<open>L\<^sub>0\<close>

definition L\<^sub>0 :: lang
  where L0_def[simp]: "L\<^sub>0 \<equiv> L\<^sub>D \<inter> SQ"



(* Lemma 4.6, p15 *)
theorem dens_L0: "dens L\<^sub>0 n \<le> dsqrt n" oops


end (* locale *)

end
