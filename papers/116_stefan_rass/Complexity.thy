theory Complexity
  imports TM Goedel_Numbering
begin

subsubsection\<open>Time\<close>

text\<open>The time restriction predicate is similar to \<^term>\<open>Hoare_halt\<close>,
  but includes a maximum number of steps.
  From Hopcroft, p287f:
   "If for every input word of length n, M makes at most T(n) moves before
    halting, then M is said to be a T(n) time-bounded Turing machine, or of time
    complexity T(n). The language recognized by M is said to be of time complexity T(n)."

   "[...] it is reasonable to assume that any time complexity function \<open>T(n)\<close> is
    at least \<open>n + 1\<close>, for this is the time needed just to read the input and verify that the
    end has been reached by reading the first blank.\<dagger> We thus make the convention
    that "time complexity \<open>T(n)\<close>" means \<open>max (n + 1, \<lceil>T(n)\<rceil>])\<close>. For example, the value of
    time complexity \<open>n log\<^sub>2n\<close> at \<open>m = 1\<close> is \<open>2\<close>, not \<open>0\<close>, and at \<open>n = 2\<close>, its value is \<open>3\<close>.

    \<dagger> Note, however, that there are TM's that accept or reject without reading all their input.
      We choose to eliminate them from consideration."\<close>

(* TODO consider turning \<open>tcomp\<close> into a definition to avoid large proof terms *)
abbreviation tcomp :: "(nat \<Rightarrow> 'c::floor_ceiling) \<Rightarrow> nat \<Rightarrow> nat"
  where "tcomp T n \<equiv> max (n + 1) (nat \<lceil>T n\<rceil>)"

abbreviation (input) tcomp\<^sub>w :: "(nat \<Rightarrow> 'c :: floor_ceiling) \<Rightarrow> 'b::blank list \<Rightarrow> nat"
  where "tcomp\<^sub>w T w \<equiv> tcomp T (tp_size <w>\<^sub>t\<^sub>p)"

lemma tcomp_mono: "(\<And>n. T n \<ge> t n) \<Longrightarrow> tcomp T n \<ge> tcomp t n" unfolding Let_def
  by (intro nat_mono max.mono of_nat_mono add_right_mono ceiling_mono) rule

context TM begin

definition time_bounded_word :: "(nat \<Rightarrow> 'c::floor_ceiling) \<Rightarrow> 'b list \<Rightarrow> bool"
  where time_bounded_def[simp]: "time_bounded_word T w \<equiv> \<exists>n.
            n \<le> tcomp\<^sub>w T w \<and> is_final (run n w)"

abbreviation time_bounded :: "(nat \<Rightarrow> 'c::floor_ceiling) \<Rightarrow> bool"
  where "time_bounded T \<equiv> \<forall>w. time_bounded_word T w"

(* TODO (?) notation: \<open>p terminates_in_time T\<close> *)

lemma
  shows tcomp_altdef1: "nat (max ((int n) + 1) \<lceil>T(n)\<rceil>) = tcomp T n" (is "?def1 = tcomp T n")
    and tcomp_altdef2: "nat (max (int (n + 1)) \<lceil>T(n)\<rceil>) = tcomp T n" (is "?def2 = tcomp T n")
proof -
  have h1: "int (n + 1) = int n + 1" by simp
  have h2: "nat (int n + 1) = n + 1" by (fold h1) (fact nat_int)
  have h3: "nat (int n + 1) \<le> nat \<lceil>T n\<rceil> \<longleftrightarrow> int n + 1 \<le> \<lceil>T n\<rceil>" by (rule nat_le_eq_zle) simp

  have "tcomp T n = max (nat (int n + 1)) (nat \<lceil>T(n)\<rceil>)" unfolding h2 ..
  also have "... = ?def1" unfolding max_def if_distrib[of nat] h3 ..
  finally show "?def1 = tcomp T n" ..
  then show "?def2 = tcomp T n" unfolding h1 .
qed

lemma tcomp_min: "tcomp f n \<ge> n + 1" by simp

lemma tcomp_eq: "f n \<ge> n + 1 \<Longrightarrow> tcomp f n = f n"
  unfolding max_def if_distrib[of nat] by (subst if_P) auto

lemma time_boundedI: "is_final (run (tcomp\<^sub>w T w) w) \<Longrightarrow> time_bounded_word T w"
  unfolding time_bounded_def by blast

lemma time_bounded_altdef:
  assumes "wf_word w"
  shows "time_bounded_word T w \<longleftrightarrow> is_final (run (tcomp\<^sub>w T w) w)"
proof
  from \<open>wf_word w\<close> have wfc: "wf_config (start_config w)" by (fact wf_start_config)

  assume "time_bounded_word T w"
  then obtain n where "n \<le> tcomp\<^sub>w T w" and "is_final (run n w)"
    unfolding time_bounded_def by blast
  then show "is_final (run (tcomp\<^sub>w T w) w)" by (fact final_mono[OF wfc])
qed (fact time_boundedI)

lemma time_boundedE:
  "wf_word w \<Longrightarrow> time_bounded T \<Longrightarrow> is_final (run (tcomp\<^sub>w T w) w)"
  using time_bounded_altdef by blast

lemma tcomp_mono: "T n \<ge> t n \<Longrightarrow> tcomp T n \<ge> tcomp t n" unfolding Let_def
  by (intro nat_mono max.mono of_nat_mono add_right_mono ceiling_mono) (rule le_refl)

lemma time_bounded_word_mono':
  fixes T t w
  assumes Tt: "tcomp\<^sub>w T w \<ge> tcomp\<^sub>w t w"
    and tr: "time_bounded_word t w"
  shows "time_bounded_word T w"
  using tr Tt unfolding time_bounded_def
proof -
  from tr obtain n where n_tcomp: "n \<le> tcomp\<^sub>w t w"
                     and final_n: "is_final (run n w)"
    unfolding time_bounded_def by blast
 from n_tcomp Tt have "n \<le> tcomp\<^sub>w T w" by (fact le_trans)
  with final_n show "\<exists>n\<le>tcomp\<^sub>w T w. is_final (run n w)" by blast
qed

lemma time_bounded_word_mono:
  fixes T t w
  defines l: "l \<equiv> tp_size <w>\<^sub>t\<^sub>p"
  assumes Tt: "T l \<ge> t l"
    and tr: "time_bounded_word t w"
  shows "time_bounded_word T w"
  using tr Tt unfolding l by (intro time_bounded_word_mono'[of w t T] tcomp_mono)

lemma time_bounded_mono':
  fixes T t
  assumes Tt: "\<And>w::'b list. tcomp\<^sub>w T w \<ge> tcomp\<^sub>w t w"
    and tr: "time_bounded t"
  shows "time_bounded T"
proof
  fix w show "time_bounded_word T w"
    using Tt[of w] tr time_bounded_word_mono'[of w t T] by fast
qed

lemma time_bounded_mono:
  fixes T t
  assumes Tt: "\<And>n. T n \<ge> t n"
    and tr: "time_bounded t"
  shows "time_bounded T"
using assms by (intro time_bounded_mono'[of t T] tcomp_mono)


text\<open>\<open>time\<^sub>M(w)\<close> is the number of steps until the computation of \<open>M\<close> halts on input \<open>w\<close>,
  or \<open>None\<close> if \<open>M\<close> does not halt on input \<open>w\<close>.\<close>

definition time :: "'b list \<Rightarrow> nat option"
  where "time w \<equiv> (
    if \<exists>n. is_final (run n w)
      then Some (LEAST n. is_final (run n w))
      else None
    )"

lemma time_Some_D: "time w = Some n \<Longrightarrow> \<exists>n. is_final (run n w)"
  by (metis option.discI time_def)

lemma halts_time: "halts w \<Longrightarrow> \<exists>n. time w = Some n"
  unfolding halts_def hoare_halt_def time_def start_config_def
  using wf_config_run wf_start_config by fastforce

lemma time_halts: "wf_word w \<Longrightarrow> time w = Some n \<Longrightarrow> halts w"
  using TM_axioms by (intro halts_I TM.time_Some_D)

lemma halts_altdef: "halts w \<longleftrightarrow> wf_word w \<and> (\<exists>n. time w = Some n)"
  using halts_time time_halts TM.halts_def TM_axioms by blast

lemma (in Rej_TM) rej_TM_time: "time w = Some 0"
proof -
  have "is_final (run 0 w)"
    unfolding start_config_def unfolding Rejecting_TM_def by simp
  thus ?thesis unfolding time_def
    using Least_eq_0 by presburger
qed

end \<comment> \<open>context \<^locale>\<open>TM\<close>\<close>


text\<open>Notion of time-constructible from Hopcroft ch. 12.3, p. 299:
  "A function T(n) is said to be time constructible if there exists a T(n) time-
  bounded multitape Turing machine M such that for each n there exists some input
  on which M actually makes T(n) moves."\<close>

definition tconstr :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "tconstr T \<equiv> \<exists>M::(nat, nat) TM. \<forall>n. \<exists>w. TM.time M w = Some (T n)"

text\<open>Fully time-constructible, ibid.:
  "We say that T(n) is fully time-constructible if there is a TM
  that uses T(n) time on all inputs of length n."\<close>

definition fully_tconstr :: "'a itself \<Rightarrow> 'b::blank itself \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "fully_tconstr TYPE('a) TYPE('b) T \<equiv>
    \<exists>M::('a, 'b) TM. \<forall>n w. length w = n \<longrightarrow> TM.time M w = Some (T n)"

lemma ftc_altdef: "fully_tconstr TYPE('a) TYPE('b::blank) T \<longleftrightarrow>
                   (\<exists>M::('a, 'b) TM. \<forall>w. TM.time M w = Some (T (length w)))"
  unfolding fully_tconstr_def by simp

lemma (in TM) time_bounded_altdef2:
  "time_bounded T \<longleftrightarrow> (\<forall>w. \<exists>n. time w = Some n \<and> n \<le> tcomp\<^sub>w T w)"
  unfolding time_bounded_def
proof (intro iffI allI exI conjI)
  fix w
  let ?f = "\<lambda>n. is_final (run n w)" let ?lf = "LEAST n. ?f n"

  assume (* time_bounded T p *) "\<forall>w. \<exists>n \<le> tcomp\<^sub>w T w. is_final (run n w)"
  then have n_ex: "\<exists>n. n \<le> tcomp\<^sub>w T w \<and> ?f n" ..
  then obtain n where "n \<le> tcomp\<^sub>w T w" and "?f n" by blast

  from n_ex have "\<exists>n. ?f n" by blast
  then show "time w = Some ?lf" unfolding time_def by (rule if_P)
  have "?lf \<le> n" using Least_le \<open>?f n\<close> .
  also note \<open>n \<le> tcomp\<^sub>w T w\<close>
  finally show "?lf \<le> tcomp\<^sub>w T w" .
next
  fix w
  let ?f = "\<lambda>n. is_final (run n w)" let ?lf = "LEAST n. ?f n"

  assume "\<forall>w. \<exists>n. time w = Some n \<and> n \<le> tcomp\<^sub>w T w"
  then obtain n where n_some: "time w = Some n" and n_le: "n \<le> tcomp\<^sub>w T w" by blast

  from n_some have "time w \<noteq> None" by (rule option.discI)
  then have n_ex: "\<exists>n. ?f n" unfolding time_def by argo
  with n_some have "?lf = n" unfolding time_def by simp

  show "?f ?lf" using LeastI_ex n_ex .
  show "?lf \<le> tcomp\<^sub>w T w" unfolding \<open>?lf = n\<close> using n_le .
qed

corollary (in TM) time_bounded_time: "time_bounded T \<Longrightarrow> the (time w) \<le> tcomp\<^sub>w T w"
  unfolding time_bounded_altdef2
proof (elim allE exE conjE)
  fix w n
  assume some_n: "time w = Some n" and n_le: "n \<le> tcomp\<^sub>w T w"
  from n_le show "the (time w) \<le> tcomp\<^sub>w T w" unfolding some_n option.sel .
qed

definition computable_in_time :: "'a itself \<Rightarrow> (nat \<Rightarrow> 'c :: floor_ceiling) \<Rightarrow> ('b::blank list \<Rightarrow> 'b list) \<Rightarrow> bool"
  where "computable_in_time TYPE('a) T f \<equiv> \<exists>M::('a, 'b) TM. TM M \<and> TM.computes M f \<and> TM.time_bounded M T"

lemma computableE[elim]:
  assumes "computable_in_time TYPE('a) T f"
  obtains M::"('a, 'b::blank) TM" where "TM.computes M f" and "TM.time_bounded M T" and "TM M"
using assms that unfolding computable_in_time_def by blast

subsection\<open>DTIME\<close>

text\<open>\<open>DTIME(T)\<close> is the set of languages decided by TMs in time \<open>T\<close> or less.\<close>
definition typed_DTIME :: "'a itself \<Rightarrow> (nat \<Rightarrow> 'c :: floor_ceiling) \<Rightarrow> ('b::blank) lang set" where
  "typed_DTIME TYPE('a) T \<equiv> {L. \<exists>M::('a, 'b) TM. TM M \<and> TM.decides M L \<and> TM.time_bounded M T}"

abbreviation DTIME where
  "DTIME \<equiv> typed_DTIME TYPE(nat)"


lemma (in TM) in_dtimeI[intro]:
  assumes "decides L"
    and "time_bounded T"
  shows "L \<in> typed_DTIME TYPE('a) T"
  unfolding typed_DTIME_def using assms TM_axioms by blast

lemma in_dtimeE[elim]:
  assumes "L \<in> typed_DTIME TYPE('a) T"
  obtains M::"('a, 'b::blank) TM"
  where "TM.decides M L"
    and "TM.time_bounded M T"
    and "TM M"
  using assms unfolding typed_DTIME_def by blast

lemma in_dtimeE'[elim]:
  assumes "L \<in> typed_DTIME TYPE('a) T"
  shows "\<exists>M::('a, 'b::blank) TM. TM M \<and> TM.decides M L \<and> TM.time_bounded M T"
  using assms unfolding typed_DTIME_def ..

corollary in_dtime_mono':
  fixes T t
  assumes "\<And>n. tcomp T n \<ge> tcomp t n"
    and "L \<in> typed_DTIME TYPE('a) t"
  shows "L \<in> typed_DTIME TYPE('a) T"
  using assms TM.time_bounded_mono' by (elim in_dtimeE, intro TM.in_dtimeI) blast+

corollary in_dtime_mono:
  fixes T t
  assumes "\<And>n. t n \<le> T n"
    and "L \<in> typed_DTIME TYPE('a) t"
  shows "L \<in> typed_DTIME TYPE('a) T"
  using assms by (intro in_dtime_mono'[of t T] tcomp_mono)

subsection\<open>Classical Results\<close>

subsubsection\<open>Almost Everywhere\<close>
context TM begin
definition "alm_all P \<equiv> finite {w \<in> wf_words. \<not> P w}"

lemma alm_all_altdef: "alm_all P \<longleftrightarrow> (MOST w. w \<notin> wf_words \<or> P w)"
  unfolding eventually_cofinite alm_all_def by simp

lemma ae_word_length_iff[iff]:
  fixes P :: "'b list \<Rightarrow> bool"
  shows "alm_all P \<longleftrightarrow> (\<exists>n. \<forall>w\<in>wf_words. length w \<ge> n \<longrightarrow> P w)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then obtain n where "P w" if "length w \<ge> n" "w \<in> wf_words" for w by blast
  then have "\<not> P w \<Longrightarrow> length w \<le> n \<or> w\<notin>wf_words" for w by auto
  then have "{w\<in>wf_words. \<not> P w} \<subseteq> {w\<in>wf_words. length w \<le> n}" by auto
  moreover have "finite {w\<in>wf_words. length w \<le> n}"
    using words_length_finite .
  ultimately show ?lhs unfolding alm_all_def by (rule finite_subset)
next
  assume ?lhs
  then have "finite {w\<in>wf_words. \<not> P w}" unfolding alm_all_def .
  show ?rhs proof (cases "{x\<in>wf_words. \<not> P x} = {}")
    assume "{x\<in>wf_words. \<not> P x} \<noteq> {}"
    define n where "n = Suc (Max (length ` {x\<in>wf_words. \<not> P x}))"

    have "P x" if "length x \<ge> n" "x\<in>wf_words" for x
    proof -
      from \<open>length x \<ge> n\<close> have "length x > Max (length ` {x\<in>wf_words. \<not> P x})"
        unfolding n_def by (fact Suc_le_lessD)
      then have "length x \<notin> length ` {x\<in>wf_words. \<not> P x}"
        using \<open>{x\<in>wf_words. \<not> P x} \<noteq> {}\<close> \<open>finite {x\<in>wf_words. \<not> P x}\<close> by (subst (asm) Max_less_iff) blast+
      then show "P x" using that(2) by blast
    qed
    then show ?rhs by blast
  qed blast
qed

lemma ae_word_lengthI:
  fixes P :: "'b list \<Rightarrow> bool"
  assumes "\<exists>n. \<forall>w\<in>wf_words. length w \<ge> n \<longrightarrow> P w"
  shows "alm_all P"
  unfolding ae_word_length_iff using assms by simp

lemma ae_word_lengthE[elim]:
  fixes P :: "'b list \<Rightarrow> bool"
  assumes "alm_all P"
  obtains n where "\<And>w. w\<in>wf_words \<Longrightarrow> length w \<ge> n \<Longrightarrow> P w"
  using assms unfolding ae_word_length_iff by fast

lemma ae_disj: "alm_all P \<or> alm_all Q \<Longrightarrow> alm_all (\<lambda>x. P x \<or> Q x)"
  by auto

lemma ae_conj_iff: "alm_all (\<lambda>x. P x \<and> Q x) \<longleftrightarrow> alm_all P \<and> alm_all Q"
  unfolding alm_all_altdef MOST_conj_distrib[symmetric] disj_conj_distribL ..

lemma ae_conjI:
  assumes "alm_all P" "alm_all Q"
  shows "alm_all (\<lambda>x. P x \<and> Q x)"
  unfolding ae_conj_iff using assms ..

end


text\<open>"Lemma 12.3  If \<open>L\<close> is accepted by a TM \<open>M\<close> that is \<open>S(n)\<close> space bounded a.e., then \<open>L\<close> is
  accepted by an \<open>S(n)\<close> space-bounded TM.
  Proof  Use the finite control to accept or reject strings of length \<open>n\<close> for the finite
  number of \<open>n\<close> where \<open>M\<close> is not \<open>S(n)\<close> bounded. Note that the construction is not
  effective, since in the absence of a time bound we cannot tell which of these words
  \<open>M\<close> accepts."

  The lemma is only stated for space bounds,
  but it seems reasonable that a similar construction works on time bounds.\<close>

lemma DTIME_ae:
  assumes "\<exists>M::('a, 'b::blank) TM. TM.alm_all M (\<lambda>w. TM.decides_word M L w \<and> TM.time_bounded_word M T w)"
  shows "L \<in> typed_DTIME TYPE('a) T"
sorry

lemma (in TM) DTIME_aeI:
  assumes "\<And>w. wf_word w \<Longrightarrow> n \<le> length w \<Longrightarrow> decides_word L w"
    and "\<And>w. wf_word w \<Longrightarrow> n \<le> length w \<Longrightarrow> time_bounded_word T w"
  shows "L \<in> typed_DTIME TYPE('a) T"
  using assms by (intro DTIME_ae) blast

lemma DTIME_mono_ae':
  fixes L :: "('b::blank) lang"
  assumes Tt: "\<And>n. N \<le> n \<Longrightarrow> tcomp T n \<ge> tcomp t n"
    and "L \<in> typed_DTIME TYPE('a) t"
  shows "L \<in> typed_DTIME TYPE('a) T"
proof -
  from \<open>L \<in> typed_DTIME TYPE('a) t\<close>
  obtain M::"('a, 'b) TM"
    where wf: "TM M" and decides: "TM.decides M L" and "TM.time_bounded M t" ..

  from wf interpret TM M .

  from decides have "alm_all (decides_word L)" by fast
  moreover have "alm_all (time_bounded_word T)"
  proof (intro ae_word_lengthI exI allI impI, safe)
    fix w :: "'b list"
    assume "length w \<ge> Suc N"
    then have "w \<noteq> []" by force
    then have tp_len: "tp_size <w>\<^sub>t\<^sub>p = length w" unfolding input_tape_def by force
    from \<open>length w \<ge> Suc N\<close> have "tp_size <w>\<^sub>t\<^sub>p \<ge> N" unfolding tp_len by (fact Suc_leD)
    then have "tcomp\<^sub>w T w \<ge> tcomp\<^sub>w t w" by (fact Tt)
    moreover from \<open>time_bounded t\<close> have "time_bounded_word t w" ..
    ultimately show "time_bounded_word T w" by (fact time_bounded_word_mono')
  qed
  ultimately show ?thesis using DTIME_ae[of L T] TM.ae_conjI wf by blast
qed

lemma DTIME_mono_ae:
  assumes Tt: "\<And>n. n \<ge> N \<Longrightarrow> T n \<ge> t n"
    and "L \<in> typed_DTIME TYPE('a) t"
  shows "L \<in> typed_DTIME TYPE('a) T"
  using assms by (intro DTIME_mono_ae'[of N t T]) (rule tcomp_mono)

subsubsection\<open>Linear Speed-Up\<close>

text\<open>Hopcroft:
 "Theorem 12.3  If \<open>L\<close> is accepted by a \<open>k\<close>-tape \<open>T(n)\<close> time-bounded Turing machine
  \<open>M\<^sub>1\<close>, then \<open>L\<close> is accepted by a \<open>k\<close>-tape \<open>cT(n)\<close> time-bounded TM \<open>M\<^sub>2\<close> for any \<open>c > 0\<close>,
  provided that \<open>k > 1\<close> and \<open>inf\<^sub>n\<^sub>\<rightarrow>\<^sub>\<infinity> T(n)/n = \<infinity>\<close>."
\<close>

definition "unbounded f \<equiv> \<forall>S. \<exists>n0. \<forall>n\<ge>n0. S \<le> f n"

lemma linear_time_speed_up:
  assumes "c > 0"
  \<comment> \<open>This assumption is stronger than the \<open>lim inf\<close> required by Hopcroft, but simpler to define in Isabelle.\<close>
    and "unbounded (\<lambda>n. T(n)/n)"
    and "TM M1"
    and "TM.decides M1 L"
    and "TM.time_bounded M1 T"
  obtains M2 where "TM M2" and "TM.decides M2 L" and "TM.time_bounded M2 (\<lambda>n. c * T n)"
  sorry


lemma dominatesE:
  fixes T :: "nat \<Rightarrow> real" and c :: real
  assumes "unbounded (\<lambda>n. T(n)/n)"
  obtains n0 where "\<And>n. n0 \<le> n \<Longrightarrow> T(n) \<ge> c*n"
proof -
  from assms obtain N where N: "T(n)/n \<ge> c" if "n \<ge> N" for n
    unfolding unbounded_def by blast

  then have "T(n) \<ge> c*n" if "n \<ge> Suc N" (is "n \<ge> ?n") for n
  proof -
    from \<open>n \<ge> Suc N\<close> have "n \<ge> N" by (fact Suc_leD)
    with N have "T(n)/n \<ge> c" .
    moreover from \<open>n \<ge> Suc N\<close> have "real n > 0" by simp
    ultimately show "T(n) \<ge> c*n" by (subst (asm) pos_le_divide_eq)
  qed
  then show ?thesis by (rule that)
qed

lemma dominatesE':
  fixes T :: "nat \<Rightarrow> real" and c :: real
  assumes "unbounded (\<lambda>n. T(n)/n)"
  shows "\<exists>n0. \<forall>n\<ge>n0. T(n) \<ge> c*n"
  using assms by (elim dominatesE) blast

corollary DTIME_speed_up:
  fixes L::"'b::blank lang"
  assumes "c > 0"
    and "unbounded (\<lambda>n. T(n)/n)"
    and "L \<in> typed_DTIME TYPE('a1) T"
  shows "L \<in> typed_DTIME TYPE('a2) (\<lambda>n. c * T n)"
proof -
  from \<open>L \<in> typed_DTIME TYPE('a1) T\<close> obtain M1::"('a1, 'b::blank) TM"
    where "TM M1" and "TM.decides M1 L" and "TM.time_bounded M1 T" ..
  with assms(1-2) obtain M2::"('a2, 'b::blank) TM"
    where "TM M2" "TM.decides M2 L" "TM.time_bounded M2 (\<lambda>n. c * T n)"
    by (rule linear_time_speed_up)
  then show ?thesis unfolding typed_DTIME_def by blast
qed

lemma DTIME_speed_up_rev:
  fixes T c
  defines "T' \<equiv> \<lambda>n. c * T n"
  assumes "c > 0"
    and "unbounded (\<lambda>n. T(n)/n)"
    and "L \<in> typed_DTIME TYPE('a1) T'"
  shows "L \<in> typed_DTIME TYPE('a2) T"
proof -
  define c' where "c' \<equiv> 1/c"
  have T: "T = (\<lambda>n. c' * T' n)" unfolding T'_def c'_def using \<open>c > 0\<close> by force

  from \<open>c > 0\<close> have "c' > 0" unfolding c'_def by simp
  moreover have "unbounded (\<lambda>n. T'(n)/n)" unfolding T'_def unbounded_def
  proof
    fix N
    define N' where "N' \<equiv> N / c"
    have *: "T(n)/n \<ge> N/c \<longleftrightarrow> c*T(n)/n \<ge> N" for n using \<open>c > 0\<close> by (subst pos_divide_le_eq) argo+

    from assms(3) have "\<exists>n'. \<forall>n\<ge>n'. T(n)/n \<ge> N'" unfolding unbounded_def ..
    then show "\<exists>n'. \<forall>n\<ge>n'. c*T(n)/n \<ge> N" unfolding N'_def * .
  qed
  moreover note \<open>L \<in> typed_DTIME TYPE('a1) T'\<close>
  ultimately show "L \<in> typed_DTIME TYPE('a2) T" unfolding T by (rule DTIME_speed_up)
qed

corollary DTIME_speed_up_eq:
  assumes "c > 0"
    and "unbounded (\<lambda>n. T(n)/n)"
  shows "typed_DTIME TYPE('a1) (\<lambda>n. c * T n) = typed_DTIME TYPE('a2) T"
  using assms by (intro set_eqI iffI) (fact DTIME_speed_up_rev, fact DTIME_speed_up)

corollary DTIME_speed_up_div:
  assumes "d > 0"
    and "unbounded (\<lambda>n. T(n)/n)"
    and "L \<in> typed_DTIME TYPE('a) T"
  shows "L \<in> typed_DTIME TYPE('a) (\<lambda>n. T n / d)"
proof -
  define c where "c \<equiv> 1 / d"
  have "a / d = c * a" for a unfolding c_def by simp

  from \<open>d > 0\<close> have "c > 0" unfolding c_def by simp
  then show "L \<in> typed_DTIME TYPE('a) (\<lambda>n. T n / d)" unfolding \<open>\<And>a. a / d = c * a\<close>
    using assms(2-3) by (rule DTIME_speed_up)
qed

subsection\<open>Reductions\<close>

lemma reduce_decides:
  fixes A B :: "'b::blank lang"
    and M\<^sub>R :: "('a1, 'b) TM" and M\<^sub>B :: "('a2, 'b) TM"
    and f\<^sub>R :: "'b list \<Rightarrow> 'b list" and w :: "'b list"
  assumes "TM.decides_word M\<^sub>B B (f\<^sub>R w)"
    and f\<^sub>R: "f\<^sub>R w \<in> B \<longleftrightarrow> w \<in> A"
    and M\<^sub>R_f\<^sub>R: "TM.computes_word M\<^sub>R f\<^sub>R w"
    and "TM M\<^sub>R"
  defines "M \<equiv> M\<^sub>R |+| M\<^sub>B"
  shows "TM.decides_word M A w"
  sorry (* likely inconsistent: see hoare_comp *)

lemma reduce_time_bounded:
  fixes T\<^sub>B T\<^sub>R :: "nat \<Rightarrow> 'c :: floor_ceiling"
    and M\<^sub>R :: "('a1, 'b::blank) TM" and  M\<^sub>B :: "('a2, 'b) TM"
    and f\<^sub>R :: "'b list \<Rightarrow> 'b list" and w :: "'b list"
  assumes "TM.time_bounded_word M\<^sub>B T\<^sub>B (f\<^sub>R w)"
    and "TM.time_bounded_word M\<^sub>R T\<^sub>R w"
    and M\<^sub>R_f\<^sub>R: "TM.computes_word M\<^sub>R f\<^sub>R w"
    and f\<^sub>R_len: "length (f\<^sub>R w) \<le> length w"
  defines "M \<equiv> M\<^sub>R |+| M\<^sub>B"
  shows "TM.time_bounded_word M (\<lambda>n. tcomp T\<^sub>R n + tcomp T\<^sub>B n) w" (is "TM.time_bounded_word M ?T w")
proof -
  define l where "l \<equiv> tp_size <w>\<^sub>t\<^sub>p"

    \<comment> \<open>Idea: We already know that the first machine \<^term>\<open>M\<^sub>R\<close> is time bounded
    (@{thm \<open>TM.time_bounded_word M\<^sub>R T\<^sub>R w\<close>}).

    We also know that its execution will result in the encoded corresponding input word \<open>f\<^sub>R w\<close>
    (@{thm \<open>TM.computes_word M\<^sub>R f\<^sub>R w\<close>}).
    Since the length of the corresponding input word is no longer
    than the length of the original input word \<^term>\<open>w\<close> (@{thm \<open>length (f\<^sub>R w) \<le> length w\<close>}),
    and the second machine \<^term>\<open>M\<^sub>B\<close> is time bounded (@{thm \<open>TM.time_bounded_word M\<^sub>B T\<^sub>B (f\<^sub>R w)\<close>}),
    we may conclude that the run-time of \<^term>\<open>M \<equiv> M\<^sub>R |+| M\<^sub>B\<close> on the input \<^term>\<open><w>\<^sub>t\<^sub>p\<close>
    is no longer than \<open>?T l = T\<^sub>R l + T\<^sub>B l\<close>.

    \<^const>\<open>TM.time_bounded\<close> is defined in terms of \<^const>\<open>tcomp\<close>, however,
    which means that the resulting total run time \<^term>\<open>?T l\<close> may be as large as
    \<^term>\<open>tcomp T\<^sub>R l + tcomp T\<^sub>B l \<equiv> nat (max (l + 1) \<lceil>T\<^sub>R l\<rceil>) + nat (max (l + 1) \<lceil>T\<^sub>B l\<rceil>)\<close>.
    If \<^term>\<open>\<lceil>T\<^sub>R l\<rceil> < l + 1\<close> or \<^term>\<open>\<lceil>T\<^sub>B l\<rceil> < l + 1\<close> then \<^term>\<open>tcomp ?T l < tcomp T\<^sub>R l + tcomp T\<^sub>B l\<close>.\<close>

  show ?thesis sorry
qed


lemma exists_ge:
  fixes P :: "'a :: linorder \<Rightarrow> bool"
  assumes "\<exists>n. \<forall>m\<ge>n. P m"
  shows "\<exists>n. \<forall>m\<ge>n. P m \<and> m \<ge> N"
proof -
  from assms obtain n where n': "P m" if "m \<ge> n" for m by blast
  then have "m \<ge> max n N \<Longrightarrow> P m \<and> m \<ge> N" for m by simp
  then show ?thesis by blast
qed

lemma exists_ge_eq:
  fixes P :: "nat \<Rightarrow> bool"
  shows "(\<exists>n. \<forall>m\<ge>n. P m) \<longleftrightarrow> (\<exists>n. \<forall>m\<ge>n. P m \<and> m \<ge> N)"
  by (intro iffI) (fact exists_ge, blast)

lemma ball_eq_simp: "(\<forall>n\<ge>x. \<forall>m. f m = n \<longrightarrow> P m) = (\<forall>m. f m \<ge> x \<longrightarrow> P m)" by blast


lemma reduce_DTIME: (* TODO clean up and tidy assumptions *)
  fixes f\<^sub>R :: "('b::blank) list \<Rightarrow> 'b list"
    and L1 L2 :: "'b list set"
  assumes f\<^sub>R_ae: "\<forall>\<^sub>\<infinity>n. \<forall>w. length w = n \<longrightarrow> (f\<^sub>R w \<in> L1) = (w \<in> L2) \<and> length (f\<^sub>R w) \<le> length w"
    and "computable_in_time TYPE('a0) T f\<^sub>R"
    and T_superlinear: "unbounded (\<lambda>n::nat. T(n)/n)"
    and "L1 \<in> typed_DTIME TYPE('a1) T"
  shows "L2 \<in> typed_DTIME TYPE('a0 + 'a1) T"
proof -
  from \<open>computable_in_time TYPE('a0) T f\<^sub>R\<close> obtain M\<^sub>R::"('a0, 'b) TM"
    where "TM.computes M\<^sub>R f\<^sub>R" "TM.time_bounded  M\<^sub>R T" "TM M\<^sub>R"
    unfolding computable_in_time_def by auto
  from \<open>L1 \<in> typed_DTIME TYPE('a1) T\<close>
  obtain M1::"('a1, 'b) TM" where "TM M1" "TM.decides M1 L1" "TM.time_bounded M1 T" ..
  define M where "M \<equiv> M\<^sub>R |+| M1"
  have "symbols M\<^sub>R = symbols M1" sorry
  with \<open>TM M\<^sub>R\<close> \<open>TM M1\<close> have "TM M" unfolding M_def by (fact wf_tm_comp)

  let ?T' = "\<lambda>n. tcomp T n + tcomp T n"

  from f\<^sub>R_ae obtain n
    where f\<^sub>R_correct: "f\<^sub>R w \<in> L1 \<longleftrightarrow> w \<in> L2"
      and f\<^sub>R_len: "length (f\<^sub>R w) \<le> length w"
    if "length w \<ge> n" for w
    unfolding MOST_nat_le ball_eq_simp by blast

  \<comment> \<open>Prove \<^term>\<open>M\<close> to be \<^term>\<open>T\<close>-time-bounded.
    Part 1: show a time-bound for \<^term>\<open>M\<close>.\<close>
  have "L2 \<in> typed_DTIME TYPE('a0+'a1) ?T'"
  proof (rule TM.DTIME_aeI)
    show "TM M" by fact

    fix w :: "'b list"
    assume min_len: "n \<le> length w"
       and "set w \<subseteq> symbols M"

    show "TM.decides_word M L2 w" unfolding M_def using \<open>TM M\<^sub>R\<close>
    proof (intro reduce_decides)
      have "pre_TM.wf_word M1 (f\<^sub>R w)" sorry (* missing assumption? *)
      with \<open>TM.decides M1 L1\<close> show "TM.decides_word M1 L1 (f\<^sub>R w)" by simp
      from f\<^sub>R_correct and min_len show "f\<^sub>R w \<in> L1 \<longleftrightarrow> w \<in> L2" .
      from \<open>TM.computes M\<^sub>R f\<^sub>R\<close> show "TM.computes_word M\<^sub>R f\<^sub>R w" ..
    qed

    show "TM.time_bounded_word M ?T' w" unfolding M_def
    proof (intro reduce_time_bounded)
      from \<open>TM.time_bounded M1 T\<close> show "TM.time_bounded_word M1 T (f\<^sub>R w)" ..
      from \<open>TM.time_bounded M\<^sub>R T\<close> show "TM.time_bounded_word M\<^sub>R T w" ..
      from \<open>TM.computes M\<^sub>R f\<^sub>R\<close> show "TM.computes_word M\<^sub>R f\<^sub>R w" ..
      from f\<^sub>R_len and min_len show "length (f\<^sub>R w) \<le> length w" .
    qed
  qed

  (* TODO (?) split proof here *)

  \<comment> \<open>Part 2: bound the run-time of M (\<^term>\<open>?T'\<close>) by a multiple of the desired time-bound \<^term>\<open>T\<close>.\<close>
  from T_superlinear have "\<exists>n. \<forall>m\<ge>n. T m \<ge> 2 * m \<and> m \<ge> 1"
    unfolding of_nat_mult by (intro exists_ge) (fact dominatesE')
  then obtain m where m: "T n \<ge> 2*n" "n \<ge> 1" if "n \<ge> m" for n by blast

  have "?T' n \<le> 4 * T n" if "n \<ge> m" for n
  proof -
    from \<open>n \<ge> m\<close> have "n \<ge> 1" and "T n \<ge> 2*n" by (fact m)+
    then have "n + 1 \<le> 2 * n" by simp
    also have "2 * n = nat \<lceil>2 * n\<rceil>" unfolding ceiling_of_nat nat_int ..
    also from \<open>T n \<ge> 2*n\<close> have "nat \<lceil>2 * n\<rceil> \<le> nat \<lceil>T n\<rceil>" by (intro nat_mono ceiling_mono)
    finally have *: "tcomp T n = nat \<lceil>T n\<rceil>" unfolding max_def by (subst if_P) auto

    from \<open>T n \<ge> 2*n\<close> \<open>n \<ge> 1\<close> have "T n \<ge> 1" by simp
    have "nat \<lceil>T n\<rceil> = real_of_int \<lceil>T n\<rceil>" using \<open>T n \<ge> 1\<close> by (intro of_nat_nat) simp
    also have "\<lceil>T n\<rceil> \<le> T n + 1" by (fact of_int_ceiling_le_add_one)
    also have "... \<le> 2 * T n" unfolding mult_2 using \<open>T n \<ge> 1\<close> by (fact add_left_mono)
    finally have "?T' n \<le> 2 * (2 * T n)" unfolding * of_nat_add mult_2 by (intro add_mono)
    also have "... = 4 * T n" by simp
    finally show ?thesis .
  qed

  from this and \<open>L2 \<in> typed_DTIME TYPE('a0+'a1) ?T'\<close>
  have "L2 \<in> typed_DTIME TYPE('a0+'a1) (\<lambda>n. 4 * T n)" by (fact DTIME_mono_ae)
  with T_superlinear show "L2 \<in> typed_DTIME TYPE('a0+'a1) T"
    by (intro DTIME_speed_up_rev[where T=T]) auto
qed

end