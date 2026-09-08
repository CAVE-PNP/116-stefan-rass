section\<open>Language Density\<close>

theory Language_Density
  imports Formal_Languages Goedel_Numbering
begin

abbreviation (input) \<epsilon> :: word where "\<epsilon> \<equiv> []" \<comment> \<open>The empty word.\<close>


text\<open>Definition of language density functions in @{cite \<open>ch.~3.1\<close> rassOwf2017}:

 ``For a language \<open>L\<close>, we define its \<^emph>\<open>density function\<close>, w.r.t. a Gödel numbering \<^const>\<open>gn\<close>,
  as the mapping
                  \<open>dens\<^sub>L : \<nat> \<rightarrow> \<nat>, x \<mapsto> |{w \<in> L : gn(w) \<le> x}|\<close>,
  i.e., \<open>dens\<^sub>L(x)\<close> is the number of words whose Gödel number as defined by [\<^const>\<open>gn\<close>]
  is bounded by \<open>x\<close>.''\<close>

definition dens :: "bool lang \<Rightarrow> nat \<Rightarrow> nat"
  where dens_def[simp]: "dens L x = card {w \<in> words L. gn w \<le> x}"

text\<open>``Occasionally, it will be convenient to let \<open>dens\<^sub>L\<close> send a word \<open>v \<in> \<Sigma>\<close> to an
  integer \<open>\<nat>\<close>, in which case we put \<open>x := (v)\<^sub>2\<close> [typo, should be \<open>(1v)\<^sub>2\<close>] in the definition of \<open>dens\<^sub>L\<close> upon an
  input word \<open>v\<close>.''\<close>

abbreviation (input) dens\<^sub>w :: "bool lang \<Rightarrow> word \<Rightarrow> nat" where
  "dens\<^sub>w L v \<equiv> dens L (gn v)"


subsection\<open>Properties\<close>

text\<open>``For every language \<open>L\<close>, the density function satisfies \<open>dens\<^sub>L(x) \<le> x\<close> for all \<open>x \<in> \<nat>\<close>.''\<close>

theorem dens_le: "dens L x \<le> x"
proof - (* shorter proof by Moritz Hiebler *)
  let ?A = "{w\<in>words L. gn w \<le> x}"
  have gn_inj_on: "inj_on gn ?A" using inj_gn by blast
  have "gn ` ?A \<subseteq> {0<..x}" by auto
  then have "card ?A \<le> card {0<..x}" using gn_inj_on finite_greaterThanAtMost
    by (intro card_inj_on_le) assumption
  then show ?thesis by (unfold card_greaterThanAtMost dens_def minus_nat.diff_0)
qed


lemma vim_nat_le:
  fixes x :: nat
  shows "{w. f w \<le> x} = f -` {0..x}"
  by fastforce

lemma vim_nat_le2:
  fixes x :: nat
  shows "{w \<in> A. f w \<le> x} = A \<inter> f -` {0..x}"
  using vim_nat_le[of f x] by blast


lemma bounded_lang_finite: "finite {w \<in> L. gn w \<le> x}"
proof -
  from inj_gn have "finite (gn -` {0..x})" using finite_vimageI[of "{0..x}" gn] by blast
  then have "finite (L \<inter> (gn -` {0..x}))" by blast
  then show "finite {w \<in> L. gn w \<le> x}" by (fold vim_nat_le2[of L gn x])
qed

lemma dens_mono: "words L\<^sub>1 \<subseteq> words L\<^sub>2 \<Longrightarrow> dens L\<^sub>1 x \<le> dens L\<^sub>2 x"
proof -
  assume "words L\<^sub>1 \<subseteq> words L\<^sub>2"
  hence "{w \<in> words L\<^sub>1. gn w \<le> x} \<subseteq> {w \<in> words L\<^sub>2. gn w \<le> x}" by blast
  with card_mono bounded_lang_finite show ?thesis unfolding dens_def .
qed

theorem dens_intersect_le[simp, intro]: "dens (L\<^sub>1 \<inter>\<^sub>L L\<^sub>2) x \<le> dens L\<^sub>2 x"
  by (intro dens_mono) simp

definition dens' :: "bool list lang \<Rightarrow> nat \<Rightarrow> nat"
  where dens'_def[simp]: "alphabet L \<subseteq> {w. length w = 2} \<Longrightarrow>
                          dens' L x = card {w \<in> words L. gn' w \<le> x}"

theorem dens'_le: "alphabet L \<subseteq> {w. length w = 2} \<Longrightarrow> dens' L x \<le> x"
proof - (* shorter proof by Moritz Hiebler *)
  assume a: "alphabet L \<subseteq> {w. length w = 2}"
  let ?A = "{w\<in>words L. gn' w \<le> x}"
  have 1: "w \<in> words L \<Longrightarrow> bin'_wf w" for w :: bin'
    using a bin'_wf_def by auto
  have gn'_inj_on: "inj_on gn' ?A" using gn'_inj_on a 1
    by (simp add: Collect_mono_iff inj_on_subset)
  have "gn' ` ?A \<subseteq> {0<..x}" by auto
  then have "card ?A \<le> card {0<..x}" using gn'_inj_on finite_greaterThanAtMost
    by (intro card_inj_on_le) assumption
  then show ?thesis by (unfold card_greaterThanAtMost dens'_def [OF a]
        minus_nat.diff_0)
qed

lemma bounded_lang_finite': "(\<And>w. w \<in> L \<Longrightarrow> set w \<subseteq> {w. length w = 2}) \<Longrightarrow>
                             finite {w \<in> L. gn' w \<le> x}"
proof -
  assume a: "\<And>w. w \<in> L \<Longrightarrow> set w \<subseteq> {w. length w = 2}"
  have "\<exists>l. {w \<in> L. gn' w \<le> x} \<subseteq> {w \<in> L. length w \<le> l}"
  proof (standard, auto)
    fix w :: bin'
    assume a1: "gn' w \<le> x" and a2: "w \<in> L"
    have "starts_with_True w \<Longrightarrow> length w \<le> Suc x"
      using a1 a2 unfolding gn'_def
    proof (induction w rule: bij_bin'_bin.induct)
      case 1
      then show ?case by simp
    next
      case (2 t)
      then show ?case by simp
    next
      case (3 t)
      then show ?case by simp
    next
      case (4 b t)
      hence False using a by fastforce
      then show ?case ..
    next
      case (5 t)
      have 1: "length (rev (flatten t) @ [False, True, True]) \<le>
               (rev (flatten t) @ [False, True, True])\<^sub>2"
        by (metis (no_types, lifting) append.right_neutral append_Cons
            ends_in_True_length_le_nat rev.simps(1) rev.simps(2) rev_append
            rev_singleton_conv)
      have 2: "length (flatten t) = 2 * length t" using a
        by (smt (verit, del_insts) "5.prems"(3) length_flatten_uniform mem_Collect_eq
            set_subset_Cons subset_code(1))
      show ?case using 1 5 apply simp
        unfolding gn_def apply simp
        apply (drule a)
        unfolding 2 by simp
    next
      case (6 t)
      have 1: "length (rev (flatten t) @ [True, True]) \<le>
               (rev (flatten t) @ [True, True])\<^sub>2"
        by (metis append.assoc append_Cons append_Nil ends_in_True_length_le_nat)
      have 2: "length (flatten t) = 2 * length t" using a
        by (smt (verit) "6.prems"(3) length_flatten_uniform mem_Collect_eq
            set_subset_Cons subset_code(1))
      show ?case using 1 6 apply simp
        unfolding gn_def by (simp add: 2)
    next
      case (7 t)
      have 1: "length (rev (flatten t) @ [True, True, True]) \<le>
               (rev (flatten t) @ [True, True, True])\<^sub>2"
        by (metis (no_types, lifting) append.assoc append_Cons
            ends_in_True_length_le_nat rev.simps(1) rev.simps(2) rev_singleton_conv)
      have 2: "length (flatten t) = 2 * length t" using a
        by (smt (verit, del_insts) "7.prems"(3) length_flatten_uniform mem_Collect_eq
            set_subset_Cons subset_code(1))
      show ?case using 7 1 apply simp
        unfolding gn_def by (simp add: 2)
    next
      case (8 b1 b2 b3 t' t)
      hence False using a by fastforce
      then show ?case .. 
    qed
    moreover have "\<not>starts_with_True w \<Longrightarrow> length w \<le> Suc x"
      using a1 a2 unfolding gn'_def
    proof (induction w rule: bij_bin'_bin.induct)
      case 1
      then show ?case by simp
    next
      case (2 t)
      hence 1: "bin'_wf t" using a
        by (simp add: bin'_wf_def subset_code(1))
      show ?case using 2(3) apply auto
        unfolding gn_def apply auto
        using ends_in_True_length_le_nat [of "bij_bin'_bin t @ [False, True]",
            simplified] length_bij_bin'_bin_ge [OF 1] by simp
    next
      case (3 t)
      then show ?case using a by fastforce
    next
      case (4 b t)
      then show ?case using a by fastforce
    next
      case (5 t)
      then show ?case by simp
    next
      case (6 t)
      then show ?case by simp
    next
      case (7 t)
      then show ?case by simp
    next
      case (8 b1 b2 b3 t' t)
      then show ?case using a by fastforce
    qed
    ultimately show "length w \<le> Suc x" by blast
  qed
  then obtain l :: nat where l_def: "{w \<in> L. gn' w \<le> x} \<subseteq> {w \<in> L. length w \<le> l}"
    by blast
  moreover have "{w \<in> L. length w \<le> l} \<subseteq>
                 {w. set w \<subseteq> {w. length w = 2} \<and> length w \<le> l}" using a by blast
  ultimately have "{w \<in> L. gn' w \<le> x} \<subseteq> {w. set w \<subseteq> {w. length w = 2} \<and> length w \<le> l}"
    by simp
  moreover have "finite {w::bin'. set w \<subseteq> {w. length w = 2} \<and> length w \<le> l}"
    using finite_list_length finite_lists_length_le by blast
  ultimately show ?thesis by (rule finite_subset)
qed

lemma dens_mono': "alphabet L\<^sub>1 \<subseteq> {w. length w = 2} \<Longrightarrow>
                   alphabet L\<^sub>2 \<subseteq> {w. length w = 2} \<Longrightarrow>
                   words L\<^sub>1 \<subseteq> words L\<^sub>2 \<Longrightarrow> dens' L\<^sub>1 x \<le> dens' L\<^sub>2 x"
proof -
  assume "words L\<^sub>1 \<subseteq> words L\<^sub>2" and a2: "alphabet L\<^sub>1 \<subseteq> {w. length w = 2}" and
         a3: "alphabet L\<^sub>2 \<subseteq> {w. length w = 2}"
  hence 1: "{w \<in> words L\<^sub>1. gn' w \<le> x} \<subseteq> {w \<in> words L\<^sub>2. gn' w \<le> x}" by blast
  with card_mono [OF bounded_lang_finite' [where x=x and L="words L\<^sub>2"] 1] a2 a3
  show ?thesis unfolding dens'_def [OF a2] dens'_def [OF a3]
    by (smt (verit, ccfv_SIG) Collect_cong lists_member member_langE order_trans)
qed

theorem dens'_intersect_le[simp, intro]:
                  "alphabet L\<^sub>2 \<subseteq> {w. length w = 2} \<Longrightarrow>
                   dens' (L\<^sub>1 \<inter>\<^sub>L L\<^sub>2) x \<le> dens' L\<^sub>2 x"
  apply (intro dens_mono') by auto
end
