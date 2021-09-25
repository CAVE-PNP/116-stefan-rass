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

abbreviation (input) tcomp :: "(nat \<Rightarrow> 'a :: floor_ceiling) \<Rightarrow> nat \<Rightarrow> nat"
  where "tcomp T n \<equiv> nat (max (n + 1) \<lceil>T(n)\<rceil>)"

abbreviation (input) tcomp\<^sub>w :: "(nat \<Rightarrow> 'a :: floor_ceiling) \<Rightarrow> 'b list \<Rightarrow> nat"
  where "tcomp\<^sub>w T w \<equiv> tcomp T (size <w>\<^sub>t\<^sub>p)"

definition (in wf_TM) time_bounded_word :: "(nat \<Rightarrow> 'c::floor_ceiling) \<Rightarrow> 'b list \<Rightarrow> bool"
  where time_bounded_def[simp]: "time_bounded_word T w \<equiv> \<exists>n.
            n \<le> tcomp\<^sub>w T w \<and> is_final (run n w)"

abbreviation (in wf_TM) time_bounded :: "(nat \<Rightarrow> 'c :: floor_ceiling) \<Rightarrow> bool"
  where "time_bounded T \<equiv> \<forall>w. time_bounded_word T w"

(* TODO (?) notation: \<open>p terminates_in_time T\<close> *)

lemma (in wf_TM) time_bounded_altdef:
  "time_bounded_word T w \<longleftrightarrow> is_final (run (tcomp\<^sub>w T w) w)"
  sorry

lemma (in wf_TM) time_boundedE:
  "time_bounded T \<Longrightarrow> is_final (run (tcomp\<^sub>w T w) w)"
  unfolding time_bounded_altdef by blast

lemma tcomp_mono: "(\<And>n. T n \<ge> t n) \<Longrightarrow> tcomp T n \<ge> tcomp t n" unfolding Let_def
  by (intro nat_mono max.mono of_nat_mono add_right_mono ceiling_mono) rule

lemma (in wf_TM) time_bounded_mono:
  fixes T t
  assumes Tt: "\<And>n. T n \<ge> t n"
    and tr: "time_bounded t"
  shows "time_bounded T"
  unfolding time_bounded_def
proof (intro allI)
  fix w
  from tr obtain n where n_tcomp: "n \<le> tcomp\<^sub>w t w"
                     and final_n: "is_final (run n w)"
    unfolding time_bounded_def by blast

  from le_trans n_tcomp tcomp_mono Tt have "n \<le> tcomp\<^sub>w T w" .
  with final_n show "\<exists>n\<le>tcomp\<^sub>w T w. is_final (run n w)" by blast
qed


text\<open>\<open>time\<^sub>M(w)\<close> is the number of steps until the computation of \<open>M\<close> halts on input \<open>w\<close>,
  or \<open>None\<close> if \<open>M\<close> does not halt on input \<open>w\<close>.\<close>

definition (in wf_TM) time :: "'b list \<Rightarrow> nat option"
  where "time w \<equiv> (
    if \<exists>n. is_final (run n w)
      then Some (LEAST n. is_final (run n w))
      else None
    )"

lemma (in wf_TM) time_Some_D: "time w = Some n \<Longrightarrow> \<exists>n. is_final (run n w)"
  by (metis option.discI time_def)

text\<open>Notion of time-constructible from Hopcroft ch. 12.3, p. 299:
  "A function T(n) is said to be time constructible if there exists a T(n) time-
  bounded multitape Turing machine M such that for each n there exists some input
  on which M actually makes T(n) moves."\<close>

definition tconstr :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "tconstr T \<equiv> \<exists>M::(nat, nat) TM. \<forall>n. \<exists>w. wf_TM.time M w = Some (T n)"

text\<open>Fully time-constructible, ibid.:
  "We say that T(n) is fully time-constructible if there is a TM
  that uses T(n) time on all inputs of length n."\<close>

definition fully_tconstr :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "fully_tconstr T \<equiv> \<exists>M::(nat, nat) TM. \<forall>n w. length w = n \<longrightarrow> wf_TM.time M w = Some (T n)"

lemma ftc_altdef: "(fully_tconstr T) \<longleftrightarrow> (\<exists>M::(nat, nat) TM. \<forall>w. wf_TM.time M w = Some (T (length w)))"
  unfolding fully_tconstr_def by simp

lemma (in wf_TM) time_bounded_altdef2:
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

corollary (in wf_TM) "time_bounded T \<Longrightarrow> the (time w) \<le> tcomp\<^sub>w T w"
  unfolding time_bounded_altdef2
proof (elim allE exE conjE)
  fix w n
  assume some_n: "time w = Some n" and n_le: "n \<le> tcomp\<^sub>w T w"
  from n_le show "the (time w) \<le> tcomp\<^sub>w T w" unfolding some_n option.sel .
qed

subsection\<open>Deciding Languages\<close>

\<comment> \<open>Since \<open>L\<close> is a typical name for unspecified languages in the literature,
    the synonymous constructor \<^term>\<open>L\<close> of type \<^typ>\<open>'b action\<close> ("move head left") is hidden.\<close>
hide_const (open) L

text\<open>A TM \<^term>\<open>p\<close> is considered to decide a language \<^term>\<open>L\<close>, iff for every possible word \<^term>\<open>w\<close>
  it correctly calculates language membership.
  That is, for \<^term>\<open>w \<in> L\<close> the computation results in \<^term>\<open>Oc\<close> under the TM head,
  and for \<^term>\<open>w \<notin> L\<close> in \<^term>\<open>Bk\<close>.\<close>

context wf_TM begin

abbreviation input where "input w \<equiv> (\<lambda>c. c = start_config w)"

lemma input_state_start_state: "input w c \<Longrightarrow> state c = start_state M"
  unfolding start_config_def by simp

definition halts :: "'b list \<Rightarrow> bool"
  where "halts w \<equiv> hoare_halt (input w) (\<lambda>_. True)"

lemma halts_I: "\<exists>n. is_final (run n w) \<Longrightarrow> halts w"
  unfolding halts_def hoare_halt_def by simp

lemma halts_time: "halts w \<Longrightarrow> \<exists>n. time w = Some n"
  unfolding halts_def hoare_halt_def time_def start_config_def by simp

lemma time_halts: "time w = Some n \<Longrightarrow> halts w"
  using time_Some_D halts_I by simp

lemma halts_altdef: "halts w \<longleftrightarrow> (\<exists>n. time w = Some n)"
  using halts_time time_halts by blast

end

type_synonym 'b lang = "'b list set"

context TM_Acc begin
definition accepts :: "'b list \<Rightarrow> bool"
  where "accepts w \<equiv> hoare_halt (input w) (\<lambda>c. state c \<in> accepting_states)"

definition rejects :: "'b list \<Rightarrow> bool"
  where "rejects w \<equiv> hoare_halt (input w) (\<lambda>c. state c \<notin> accepting_states)"

definition decides_word :: "'b lang \<Rightarrow> 'b list \<Rightarrow> bool"
  where decides_def[simp]: "decides_word L w \<equiv> (w \<in> L \<longleftrightarrow> accepts w) \<and> (w \<notin> L \<longleftrightarrow> rejects w)"

abbreviation decides :: "'b lang \<Rightarrow> bool"
  where "decides L \<equiv> \<forall>w. decides_word L w"
end

locale Rejecting_TM begin
definition "Rejecting_TM \<equiv> \<lparr>
  tape_count = 1,
  states = {1}::nat set,
  start_state = 1,
  final_states = {1},
  symbols = {B},
  next_state = \<lambda>q w. 1,
  next_action = \<lambda>q w. [Nop]
\<rparr>"
interpretation TM_Acc Rejecting_TM "{}"
  unfolding Rejecting_TM_def
  by unfold_locales simp_all

lemma rej_TM: "rejects w"
  unfolding rejects_def proof
  fix c0::"(nat, 'a::blank) TM_config"
  assume "input w c0"
  hence "state c0 = start_state Rejecting_TM"
    by (rule input_state_start_state)
  then have "is_final ((step^^0) c0)"
    unfolding is_final_def unfolding Rejecting_TM_def by simp
  thus "\<exists>n. let cn = (step ^^ n) c0 in is_final cn \<and> state cn \<notin> {}"
    unfolding empty_iff by metis
qed

lemma rej_TM_time: "time w = Some 0"
proof -
  have "is_final (run 0 w)"
    unfolding is_final_def start_config_def unfolding Rejecting_TM_def by simp
  thus ?thesis unfolding time_def
    using Least_eq_0 by presburger
qed
end

lemma (in wf_TM) hoare_true: "hoare_halt P Q \<Longrightarrow> hoare_halt P (\<lambda>_. True)"
  unfolding hoare_halt_def by metis

lemma (in TM_Acc) accepts_halts: "accepts w \<Longrightarrow> halts w"
  unfolding accepts_def halts_def by (rule hoare_true)
lemma (in TM_Acc) rejects_halts: "rejects w \<Longrightarrow> halts w"
  unfolding rejects_def halts_def by (rule hoare_true)

lemma (in wf_TM) hoare_and[intro]:
  assumes h1: "hoare_halt P Q1"
    and h2: "hoare_halt P Q2"
  shows "hoare_halt P (\<lambda>c. Q1 c \<and> Q2 c)"
proof
  fix c assume "P c"
  from \<open>P c\<close> h1 obtain n1 where fn1: "is_final ((step^^n1) c)" and q1: "Q1 ((step^^n1) c)" by rule
  from \<open>P c\<close> h2 obtain n2 where fn2: "is_final ((step^^n2) c)" and q2: "Q2 ((step^^n2) c)" by rule

  define n::nat where "n \<equiv> max n1 n2"
  hence "n1 \<le> n" "n2 \<le> n" by simp+
  with fn1 fn2 final_le_steps
  have "((step^^n1) c) = ((step^^n) c)" "((step^^n2) c) = ((step^^n) c)" by metis+
  with fn1 q1 q2 have "let qn=(step^^n) c in is_final qn \<and> Q1 qn \<and> Q2 qn" by simp
  thus "\<exists>n. let cn = (step ^^ n) c in is_final cn \<and> Q1 cn \<and> Q2 cn" ..
qed

lemma hoare_contr:
  fixes P M tp
  assumes "Hoare_halt P M (\<lambda>_. False)" and "P tp"
  shows "False"
proof - \<comment> \<open>This one is tricky since the automatic solvers do not pick apart pairs on their own.
  Since @{thm holds_for.simps} is defined in terms of pair items, it is not directly applicable.\<close>
  from assms obtain n where "(\<lambda>_. False) holds_for steps0 (1, tp) M n" ..
  moreover obtain s l r where "steps0 (1, tp) M n = (s, l, r)" using prod_cases3 .
  ultimately show "(\<lambda>_. False) (l, r)" (* \<equiv> False *) by simp
qed

lemma input_encoding: \<comment> \<open>Each word has an input encoding. Useful with @{thm hoare_contr}}\<close>
  fixes w
  shows "input w ([], encode_word (decode_word (encode_word w)))" unfolding encode_decode_word ..

lemma holds_for_neg: "\<not> Q holds_for c \<longleftrightarrow> (\<lambda>tp. \<not> Q tp) holds_for c"
proof -
  obtain s l r where c_def: "c = (s, l, r)" by (rule prod_cases3)
  show ?thesis unfolding c_def by simp
qed

lemma hoare_halt_neg:
  assumes "\<not> Hoare_halt (input w) M Q"
    and "halts M w"
  shows "Hoare_halt (input w) M (\<lambda>tp. \<not> Q tp)"
  using assms unfolding Hoare_halt_def holds_for_neg[symmetric] halts_def by fast

lemma head_halt_inj:
  assumes "Hoare_halt (input w) M (\<lambda>tp. head tp = x)"
      and "Hoare_halt (input w) M (\<lambda>tp. head tp = y)"
    shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  then have *: "a = x \<and> a = y \<longleftrightarrow> False" for a by blast

  from hoare_and have "Hoare_halt (input w) M (\<lambda>tp. head tp = x \<and> head tp = y)"
    using assms .
  then have "Hoare_halt (input w) M (\<lambda>_. False)" unfolding * .
  thus False using input_encoding by (rule hoare_contr)
qed

lemma acc_not_rej:
  assumes "accepts M w"
  shows "\<not> rejects M w"
proof (intro notI)
  assume "rejects M w"

  have "Hoare_halt (input w) M (\<lambda>tp. head tp = Oc)"
    using \<open>accepts M w\<close> unfolding accepts_def .
  moreover have "Hoare_halt (input w) M (\<lambda>tp. head tp = Bk)"
    using \<open>rejects M w\<close> unfolding rejects_def .
  ultimately show False using head_halt_inj[of w M Oc Bk] by blast
qed


lemma rejects_altdef:
  "rejects M w = (halts M w \<and> \<not> accepts M w)"
proof (intro iffI conjI)
  assume "rejects M w"
  then show "halts M w" unfolding rejects_def halts_def using hoare_true by fast
  from \<open>rejects M w\<close> show "\<not> accepts M w" using acc_not_rej by auto
next
  have *: "c \<noteq> Oc \<longleftrightarrow> c = Bk" for c by (cases c) blast+

  assume "halts M w \<and> \<not> accepts M w"
  then have "Hoare_halt (input w) M (\<lambda>tp. head tp \<noteq> Oc)"
    unfolding accepts_def by (intro hoare_halt_neg) blast+
  then show "rejects M w" unfolding rejects_def * .
qed

lemma decides_halts: "decides_word M L w \<Longrightarrow> halts M w"
  by (cases "w \<in> L") (intro accepts_halts, simp, intro rejects_halts, simp)


lemma decides_altdef1: "decides_word M L w \<longleftrightarrow> halts M w \<and> (w \<in> L \<longleftrightarrow> accepts M w)"
proof (intro iffI)
  fix w
  assume "decides_word M L w"
  hence "halts M w" by (rule decides_halts)
  moreover have "w \<in> L \<longleftrightarrow> accepts M w" using \<open>decides_word M L w\<close> by simp
  ultimately show "halts M w \<and> (w \<in> L \<longleftrightarrow> accepts M w)" ..
next
  assume "halts M w \<and> (w \<in> L \<longleftrightarrow> accepts M w)"
  then show "decides_word M L w" by (simp add: rejects_altdef)
qed

lemma decides_altdef2:
  fixes M :: TM
  shows "decides_word M L w \<longleftrightarrow> {input w} M {\<lambda>tp. head tp = (if w \<in> L then Oc else Bk)}"
    (is "?dw M L w \<longleftrightarrow> {?pre w} M {?post w}")
proof (intro iffI allI)
  assume "?dw M L w"
  then show "{?pre w} M {?post w}" unfolding decides_def accepts_def rejects_def
  proof (cases "w \<in> L")
    case False
    from \<open>?dw M L w\<close> \<open>w \<notin> L\<close> have "rejects M w" unfolding decides_def by blast
    thus ?thesis unfolding rejects_def using \<open>w \<notin> L\<close> by presburger
  qed (* case "w \<in> L" by *) presburger
next
  assume assm: "{?pre w} M {?post w}"
  show "?dw M L w" unfolding decides_def proof (intro conjI)
    show "w \<in> L \<longleftrightarrow> accepts M w" proof
      assume "w \<in> L"
      thus "accepts M w" unfolding accepts_def using assm by presburger
    next
      assume "accepts M w"
      then have "Oc = (if w\<in>L then Oc else Bk)"
        unfolding accepts_def using assm head_halt_inj[of w M Oc] by presburger
      thus "w \<in> L" using cell.distinct(1) by presburger
    qed
  next
    show "w \<notin> L \<longleftrightarrow> rejects M w" proof
      assume "w \<notin> L"
      thus "rejects M w" unfolding rejects_def using assm by presburger
    next
      assume "rejects M w"
      then have "Bk = (if w\<in>L then Oc else Bk)"
        unfolding rejects_def using assm head_halt_inj[of w M Bk] by presburger
      thus "w \<notin> L" by auto
    qed
  qed
qed

lemma decides_altdef3:
  "decides_word M L w \<longleftrightarrow> {input w} M {\<lambda>tp. head tp = Oc \<longleftrightarrow> w \<in> L}"
proof -
  have *: "(a = Oc \<longleftrightarrow> c) \<longleftrightarrow> a = (if c then Oc else Bk)" for a c by (induction a) simp_all
  show ?thesis unfolding * by (rule decides_altdef2)
qed

(* TODO (?) notation: \<open>p decides L\<close> *)


subsection\<open>DTIME\<close>

text\<open>\<open>DTIME(T)\<close> is the set of languages decided by TMs in time \<open>T\<close> or less.\<close>
definition DTIME :: "(nat \<Rightarrow> 'a :: floor_ceiling) \<Rightarrow> lang set"
  where "DTIME T \<equiv> {L. \<exists>M. decides M L \<and> time_bounded T M}"

lemma in_dtimeI[intro]:
  assumes "decides M L"
    and "time_bounded T M"
  shows "L \<in> DTIME T"
  unfolding DTIME_def using assms by blast

lemma in_dtimeE[elim]:
  assumes "L \<in> DTIME T"
  obtains M
  where "decides M L"
    and "time_bounded T M"
  using assms unfolding DTIME_def by blast

lemma in_dtimeE'[elim]:
  assumes "L \<in> DTIME T"
  shows "\<exists>M. decides M L \<and> time_bounded T M"
  using assms unfolding DTIME_def ..


corollary in_dtime_mono: 
  fixes T t
  assumes Tt: "\<And>n. T n \<ge> t n"
    and tD: "L \<in> DTIME(t)"
  shows "L \<in> DTIME(T)"
  using assms time_bounded_mono by (elim in_dtimeE, intro in_dtimeI) blast+


subsection\<open>Classical Results\<close>

subsubsection\<open>Almost Everywhere\<close>

text\<open>Hopcroft uses the finite control in Lemma 12.3
  to make the jump from almost everywhere to everywhere:

  "We say that a statement with parameter \<open>n\<close> is true \<^emph>\<open>almost everywhere\<close> (a.e.) if it
  is true for all but a finite number of values of \<open>n\<close>. We say a statement is true infinitely
  often (i.o.) if it is true for an infinite number of \<open>n\<close>'s. Note that both a statement and
  its negation may be true i.o."\<close>

definition almost_everywhere :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  where ae_def[simp]: "almost_everywhere P \<equiv> finite {x. \<not> P x}"


lemma ae_everywhereI: "(\<And>x. P x) \<Longrightarrow> almost_everywhere P" by simp

lemma word_length_ae:
  fixes P :: "word \<Rightarrow> bool"
  assumes "\<And>w. length w \<ge> n \<Longrightarrow> P w"
  shows "almost_everywhere P"
  unfolding ae_def
proof (rule finite_subset)
  have "\<not> P w \<Longrightarrow> length w < n" for w using assms by (intro not_le_imp_less) (rule contrapos_nn)
  then show "{w. \<not> P w} \<subseteq> {w. length w < n}" by (intro Collect_mono impI)
  show "finite {w::word. length w < n}" by (rule finite_bin_len_less)
qed


text\<open>"Lemma 12.3  If \<open>L\<close> is accepted by a TM \<open>M\<close> that is \<open>S(n)\<close> space bounded a.e., then \<open>L\<close> is
  accepted by an \<open>S(n)\<close> space-bounded TM.
  Proof  Use the finite control to accept or reject strings of length \<open>n\<close> for the finite
  number of \<open>n\<close> where \<open>M\<close> is not \<open>S(n)\<close> bounded. Note that the construction is not
  effective, since in the absence of a time bound we cannot tell which of these words
  \<open>M\<close> accepts."

  The lemma is only stated for space bounds,
  but it seems reasonable that a similar construction works on time bounds.\<close>


lemma DTIME_ae:
  assumes "almost_everywhere (decides_word M L)"
    and "almost_everywhere (time_bounded_word T M)"
  shows "L \<in> DTIME(T)"
  sorry


subsubsection\<open>Linear Speed-Up\<close>

text\<open>Hopcroft:

 "Theorem 12.3  If \<open>L\<close> is accepted by a \<open>k\<close>-tape \<open>T(n)\<close> time-bounded Turing machine
  \<open>M\<^sub>1\<close>, then \<open>L\<close> is accepted by a \<open>k\<close>-tape \<open>cT(n)\<close> time-bounded TM \<open>M\<^sub>2\<close> for any \<open>c > 0\<close>,
  provided that \<open>k > 1\<close> and \<open>inf\<^sub>n\<^sub>\<rightarrow>\<^sub>\<infinity> T(n)/n = \<infinity>\<close>."

  Note that the following formalization is likely false
  (or at least not provable using the construction of Hopcroft),
  as the used definition of TMs only allows single-tape TMs with a binary alphabet.\<close>

lemma linear_time_speed_up:
  assumes "c > 0"
  \<comment> \<open>This assumption is stronger than the \<open>lim inf\<close> required by Hopcroft, but simpler to define in Isabelle.\<close>
    and "\<forall>N. \<exists>n'. \<forall>n\<ge>n'. T(n)/n \<ge> N"
    and "decides M\<^sub>1 L"
    and "time_bounded T M\<^sub>1"
  obtains M\<^sub>2 where "decides M\<^sub>2 L" and "time_bounded (\<lambda>n. c * T n) M\<^sub>2"
  sorry


corollary DTIME_speed_up:
  assumes "c > 0"
    and "\<forall>N. \<exists>n'. \<forall>n\<ge>n'. T(n)/n \<ge> N"
    and "L \<in> DTIME(T)"
  shows "L \<in> DTIME(\<lambda>n. c * T n)"
proof -
  from \<open>L \<in> DTIME(T)\<close> obtain M\<^sub>1 where "decides M\<^sub>1 L" and "time_bounded T M\<^sub>1" ..
  with assms(1-2) obtain M\<^sub>2 where "decides M\<^sub>2 L" and "time_bounded (\<lambda>n. c * T n) M\<^sub>2"
    by (rule linear_time_speed_up)
  then show ?thesis ..
qed

lemma DTIME_speed_up_rev:
  fixes T c
  defines "T' \<equiv> \<lambda>n. c * T n"
  assumes "c > 0"
    and "\<forall>N. \<exists>n'. \<forall>n\<ge>n'. T(n)/n \<ge> N"
    and "L \<in> DTIME(T')"
  shows "L \<in> DTIME(T)"
proof -
  define c' where "c' \<equiv> 1/c"
  have T_T': "T = (\<lambda>n. c' * T' n)" unfolding T'_def c'_def using \<open>c > 0\<close> by force

  from \<open>c > 0\<close> have "c' > 0" unfolding c'_def by simp
  moreover have "\<forall>N. \<exists>n'. \<forall>n\<ge>n'. T'(n)/n \<ge> N" unfolding T'_def
  proof
    fix N
    define N' where "N' \<equiv> N / c"
    have *: "T(n)/n \<ge> N/c \<longleftrightarrow> c*T(n)/n \<ge> N" for n using \<open>c > 0\<close> by (subst pos_divide_le_eq) argo+

    from assms(3) have "\<exists>n'. \<forall>n\<ge>n'. T(n)/n \<ge> N'" ..
    then show "\<exists>n'. \<forall>n\<ge>n'. c*T(n)/n \<ge> N" unfolding N'_def * .
  qed
  moreover note \<open>L \<in> DTIME(T')\<close>
  ultimately show "L \<in> DTIME(T)" unfolding T_T' by (rule DTIME_speed_up)
qed

corollary DTIME_speed_up_eq:
  assumes "c > 0"
    and "\<forall>N. \<exists>n'. \<forall>n\<ge>n'. T(n)/n \<ge> N"
  shows "DTIME(\<lambda>n. c * T n) = DTIME(T)"
  using assms by (intro set_eqI iffI) (fact DTIME_speed_up_rev, fact DTIME_speed_up)

corollary DTIME_speed_up_div:
  assumes "d > 0"
    and "\<forall>N. \<exists>n'. \<forall>n\<ge>n'. T(n)/n \<ge> N"
    and "L \<in> DTIME(T)"
  shows "L \<in> DTIME(\<lambda>n. T n / d)"
proof -
  define c where "c \<equiv> 1 / d"
  have "a / d = c * a" for a unfolding c_def by simp

  from \<open>d > 0\<close> have "c > 0" unfolding c_def by simp
  then show "L \<in> DTIME(\<lambda>n. T n / d)" unfolding \<open>\<And>a. a / d = c * a\<close>
    using assms(2-3) by (rule DTIME_speed_up)
qed


subsection\<open>Reductions\<close>

lemma reduce_decides:
  fixes A B :: lang and M\<^sub>R M\<^sub>B :: TM and f\<^sub>R :: "word \<Rightarrow> word" and w :: word
  assumes "decides_word M\<^sub>B B (f\<^sub>R w)"
    and f\<^sub>R: "w \<in> A \<longleftrightarrow> f\<^sub>R w \<in> B"
    and M\<^sub>R_f\<^sub>R: "{input w} M\<^sub>R {input (f\<^sub>R w)}"
    and "tm_wf0 M\<^sub>R"
  defines "M \<equiv> M\<^sub>R |+| M\<^sub>B"
  shows "decides_word M A w"
proof -
  have "{input w} M\<^sub>R |+| M\<^sub>B {\<lambda>tp. (head tp = Oc) = (f\<^sub>R w \<in> B)}" using M\<^sub>R_f\<^sub>R \<open>tm_wf0 M\<^sub>R\<close>
  proof (intro Hoare_plus_halt)
    from \<open>decides_word M\<^sub>B B (f\<^sub>R w)\<close> show "{input (f\<^sub>R w)} M\<^sub>B {\<lambda>tp. (head tp = Oc) = (f\<^sub>R w \<in> B)}"
      unfolding decides_altdef3 .
  qed
  then have "{input w} M {\<lambda>tp. (head tp = Oc) = (w \<in> A)}" unfolding M_def \<open>w \<in> A \<longleftrightarrow> f\<^sub>R w \<in> B\<close> .
  then show "decides_word M A w" unfolding decides_altdef3 .
qed


lemma reduce_time_bounded:
  fixes T\<^sub>B T\<^sub>R :: "nat \<Rightarrow> 'a :: floor_ceiling" and M\<^sub>R M\<^sub>B :: TM and f\<^sub>R :: "word \<Rightarrow> word" and w :: word
  assumes "time_bounded_word T\<^sub>B M\<^sub>B (f\<^sub>R w)"
    and "time_bounded_word T\<^sub>R M\<^sub>R w"
    and M\<^sub>R_f\<^sub>R: "Hoare_halt (input w) M\<^sub>R (input (f\<^sub>R w))"
    and f\<^sub>R_len: "length (f\<^sub>R w) \<le> length w"
    (* and "tm_wf0 M\<^sub>R" *)
  defines "M \<equiv> M\<^sub>R |+| M\<^sub>B"
  defines "(T :: nat \<Rightarrow> 'a) \<equiv> \<lambda>n. of_nat (tcomp T\<^sub>R n + tcomp T\<^sub>B n)"
  shows "time_bounded_word T M w"
proof -
  define l where "l \<equiv> tape_size <w>\<^sub>t\<^sub>p"

    \<comment> \<open>Idea: We already know that the first machine \<^term>\<open>M\<^sub>R\<close> is time bounded
    (@{thm \<open>time_bounded_word T\<^sub>R M\<^sub>R w\<close>}),
    such that its run-time is bounded by \<^term>\<open>T\<^sub>R l = T\<^sub>R (2 * length w)\<close>
    (@{thm tape_size_input}}).

    We also know that its execution will result in the encoded corresponding input word \<open>f\<^sub>R w\<close>
    (@{thm \<open>{input w} M\<^sub>R {input (f\<^sub>R w)}\<close>}).
    Since the length of the corresponding input word is no longer
    than the length of the original input word \<^term>\<open>w\<close> (@{thm \<open>length (f\<^sub>R w) \<le> length w\<close>}),
    and the second machine \<^term>\<open>M\<^sub>B\<close> is time bounded (@{thm \<open>time_bounded_word T\<^sub>B M\<^sub>B (f\<^sub>R w)\<close>}),
    we may conclude that the run-time of \<^term>\<open>M \<equiv> M\<^sub>R |+| M\<^sub>B\<close> on the input \<^term>\<open><w>\<^sub>t\<^sub>p\<close>
    is no longer than \<^term>\<open>T l \<equiv> T\<^sub>R l + T\<^sub>B l\<close>.

    \<^const>\<open>time_bounded\<close> is defined in terms of \<^const>\<open>tcomp\<close>, however,
    which means that the resulting total run time \<^term>\<open>T l\<close> may be as large as
    \<^term>\<open>tcomp T\<^sub>R l + tcomp T\<^sub>B l \<equiv> nat (max (l + 1) \<lceil>T\<^sub>R l\<rceil>) + nat (max (l + 1) \<lceil>T\<^sub>B l\<rceil>)\<close>.
    If \<^term>\<open>\<lceil>T\<^sub>R l\<rceil> < l + 1\<close> or \<^term>\<open>\<lceil>T\<^sub>B l\<rceil> < l + 1\<close> then \<^term>\<open>tcomp T l < tcomp T\<^sub>R l + tcomp T\<^sub>B l\<close>.\<close>

  show ?thesis sorry
qed


end