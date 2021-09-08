theory THT_inconsistencies_MWE
  imports Complex_Main
    "Universal_Turing_Machine.UTM"
begin


section\<open>Definitions\<close>

type_synonym TM = "tprog0"

type_synonym bin = "bool list"
type_synonym word = "bin"
type_synonym lang = "word set"

hide_const (open) L


definition Rejecting_TM :: TM
  where "Rejecting_TM = [(W0, 0), (W0, 0)]"

definition time :: "TM \<Rightarrow> tape \<Rightarrow> nat option"
  where "time M x \<equiv> (
    if \<exists>n. is_final (steps0 (1, x) M n)
      then Some (LEAST n. is_final (steps0 (1, x) M n))
      else None
    )"

definition fully_tconstr :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "fully_tconstr T \<equiv> \<exists>M. \<forall>n w. length w = n \<longrightarrow> time M ([], w) = Some (T n)"


abbreviation head where "head tp \<equiv> read (snd tp)"

fun encode_word :: "word \<Rightarrow> cell list" where
  "encode_word [] = []"
| "encode_word (False # w) = Oc # Bk # encode_word w"
| "encode_word (True  # w) = Oc # Oc # encode_word w"
abbreviation input_tape ("<_>\<^sub>t\<^sub>p") where "<w>\<^sub>t\<^sub>p \<equiv> (([]::cell list), encode_word w)"
abbreviation input where "input w \<equiv> (\<lambda>tp. tp = <w>\<^sub>t\<^sub>p)"

fun tape_size :: "tape \<Rightarrow> nat" \<comment> \<open>using \<open>fun\<close> since \<open>definition\<close> does not recognize patterns like \<^term>\<open>(l, r)\<close>\<close>
  where "tape_size (l, r) = length l + length r"

definition accepts :: "TM \<Rightarrow> word \<Rightarrow> bool"
  where "accepts M w \<equiv> Hoare_halt (input w) M (\<lambda>tp. head tp = Oc)"
definition rejects :: "TM \<Rightarrow> word \<Rightarrow> bool"
  where "rejects M w \<equiv> Hoare_halt (input w) M (\<lambda>tp. head tp = Bk)"

definition decides_word :: "TM \<Rightarrow> lang \<Rightarrow> word \<Rightarrow> bool"
  where decides_def[simp]: "decides_word M L w \<equiv> (w \<in> L \<longleftrightarrow> accepts M w) \<and> (w \<notin> L \<longleftrightarrow> rejects M w)"
abbreviation decides :: "TM \<Rightarrow> lang \<Rightarrow> bool"
  where "decides M L \<equiv> \<forall>w. decides_word M L w "

abbreviation (input) tcomp :: "(nat \<Rightarrow> 'a :: floor_ceiling) \<Rightarrow> nat \<Rightarrow> nat"
  where "tcomp T n \<equiv> nat (max (n + 1) \<lceil>T(n)\<rceil>)"
abbreviation (input) tcomp\<^sub>w :: "(nat \<Rightarrow> 'a :: floor_ceiling) \<Rightarrow> word \<Rightarrow> nat"
  where "tcomp\<^sub>w T w \<equiv> tcomp T (tape_size <w>\<^sub>t\<^sub>p)"

definition time_bounded_word :: "(nat \<Rightarrow> 'a :: floor_ceiling) \<Rightarrow> TM \<Rightarrow> word \<Rightarrow> bool"
  where time_bounded_def[simp]: "time_bounded_word T M w \<equiv> \<exists>n.
            n \<le> tcomp\<^sub>w T w \<and> is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M n)"
abbreviation time_bounded :: "(nat \<Rightarrow> 'a :: floor_ceiling) \<Rightarrow> TM \<Rightarrow> bool"
  where "time_bounded T M \<equiv> \<forall>w. time_bounded_word T M w"

definition DTIME :: "(nat \<Rightarrow> 'a :: floor_ceiling) \<Rightarrow> lang set"
  where "DTIME T \<equiv> {L. \<exists>M. decides M L \<and> time_bounded T M}"


section\<open>Lemmas\<close>

lemma rej_TM_step1: "steps0 (1, (l, r)) Rejecting_TM 1 = (0, l, Bk # tl r)"
proof -
  have fetch: "fetch Rejecting_TM 1 b = (W0, 0)" for b unfolding Rejecting_TM_def
    by (cases b) (simp_all add: fetch.simps nth_of.simps)

  have "steps0 (1, (l, r)) Rejecting_TM 1 = step0 (1, l, r) Rejecting_TM"
    unfolding One_nat_def steps.simps ..
  also have "... = (0, update W0 (l, r))" unfolding step.simps diff_zero fetch by simp
  also have "... = (0, l, Bk # tl r)" by simp
  finally show ?thesis .
qed

lemma rej_TM_time: "time Rejecting_TM tp = Some 1"
proof -
  let ?f = "\<lambda>n. is_final (steps0 (1, tp) Rejecting_TM n)"

  obtain l r where tp: "tp = (l, r)" by (rule prod.exhaust)
  have "\<not> ?f 0" unfolding steps.simps tp is_final.simps by (rule one_neq_zero)
  have "?f 1" unfolding tp rej_TM_step1 ..
  then have c: "\<exists>n. ?f n" ..

  then have "time Rejecting_TM tp = Some (LEAST n. ?f n)" unfolding time_def by (rule if_P)
  also have "... = Some 1"
  proof (intro arg_cong[where f=Some] Least_equality)
    fix n assume "?f n"
    show "n \<ge> 1" proof (rule ccontr, unfold not_le)
      assume "n < 1"
      then have "n = 0" unfolding One_nat_def less_Suc0 .
      from \<open>?f n\<close> have "?f 0" unfolding \<open>n = 0\<close> .
      with \<open>\<not> ?f 0\<close> show False by contradiction
    qed
  qed fact
  finally show ?thesis .
qed


section\<open>Assumptions\<close>

theorem time_hierarchy: 
  fixes T t :: "nat \<Rightarrow> nat"
  assumes "fully_tconstr T"
    and "lim (\<lambda>l. t l * log 2 (t l) / T l) = 0"
  shows "\<exists>L. L \<in> DTIME T - DTIME t"
  sorry


section\<open>Result\<close>

corollary False
proof -
  define T :: "nat \<Rightarrow> nat" where "T \<equiv> \<lambda>n. 1"

  have "fully_tconstr T" unfolding fully_tconstr_def T_def
    by (intro exI allI impI) (rule rej_TM_time)
  moreover have "lim (\<lambda>l. T l * log 2 (T l) / T l) = 0" unfolding T_def by force
  ultimately have "\<exists>L. L \<in> DTIME(T) - DTIME(T)" by (rule time_hierarchy)
  then show False by blast
qed

end
