section\<open>Language Density\<close>

theory Language_Density
  imports Goedel_Numbering
begin

type_synonym lang = "word set"

abbreviation (input) \<epsilon> :: word where "\<epsilon> \<equiv> []" \<comment> \<open>The empty word.\<close>


text\<open>Definition of language density functions in @{cite \<open>ch.~3.1\<close> rassOwf2017}:

 ``For a language \<open>L\<close>, we define its \<^emph>\<open>density function\<close>, w.r.t. a Gödel numbering \<^const>\<open>gn\<close>,
  as the mapping
                  \<open>dens\<^sub>L : \<nat> \<rightarrow> \<nat>, x \<mapsto> |{w \<in> L : gn(w) \<le> x}|\<close>,
  i.e., \<open>dens\<^sub>L(x)\<close> is the number of words whose Gödel number as defined by [\<^const>\<open>gn\<close>]
  is bounded by \<open>x\<close>.''\<close>

definition dens :: "lang \<Rightarrow> nat \<Rightarrow> nat"
  where dens_def[simp]: "dens L x = card {w \<in> L. gn w \<le> x}"

text\<open>``Occasionally, it will be convenient to let \<open>dens\<^sub>L\<close> send a word \<open>v \<in> \<Sigma>\<close> to an
  integer \<open>\<nat>\<close>, in which case we put \<open>x := (v)\<^sub>2\<close> in the definition of \<open>dens\<^sub>L\<close> upon an
  input word \<open>v\<close>.''\<close>

abbreviation (input) dens\<^sub>w :: "lang \<Rightarrow> word \<Rightarrow> nat" where
  "dens\<^sub>w L v \<equiv> dens L (gn v)"


subsection\<open>Properties\<close>

lemma inj_spec: "inj f \<Longrightarrow> inj_on f A" by (rule inj_on_subset[where A=UNIV]) blast+

text\<open>``For every language \<open>L\<close>, the density function satisfies \<open>dens\<^sub>L(x) \<le> x\<close> for all \<open>x \<in> \<nat>\<close>.''\<close>

theorem dens_le: "dens L x \<le> x"
proof - (* shorter proof by Moritz Hiebler *)
  let ?A = "{w\<in>L. gn w \<le> x}"
  have gn_inj_on: "inj_on gn ?A"
    using inj_gn inj_spec by blast
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

lemma dens_mono: "L\<^sub>1 \<subseteq> L\<^sub>2 \<Longrightarrow> dens L\<^sub>1 x \<le> dens L\<^sub>2 x"
proof -
  assume "L\<^sub>1 \<subseteq> L\<^sub>2"
  hence "{w \<in> L\<^sub>1. gn w \<le> x} \<subseteq> {w \<in> L\<^sub>2. gn w \<le> x}" by blast
  with card_mono bounded_lang_finite show ?thesis unfolding dens_def .
qed

theorem dens_intersect_le: "dens (L\<^sub>1 \<inter> L\<^sub>2) x \<le> dens L\<^sub>2 x"
  by (intro dens_mono) (rule Int_lower2)

end
