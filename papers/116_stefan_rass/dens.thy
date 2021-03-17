theory dens
  imports Main HOL.Num
begin

(*
  words are binary strings which can be represented by num by appending 1
  empty word \<rightarrow> 1
  0000       \<rightarrow> 10000
  101010     \<rightarrow> 1101010
  w          \<rightarrow> 1w

  Using this representation, the Gödel numbering gn: word \<Rightarrow> nat
  from the paper is just the function nat_of_num
*)
type_synonym word = "num"
fun length :: "word \<Rightarrow> nat" where
 "length num.One = 0" |
 "length (num.Bit0 x) = Suc (length x)" |
 "length (num.Bit1 x) = Suc (length x)"

lemma nat_of_num_inj: "inj nat_of_num"
  using num_eq_iff by (simp add: injI)

type_synonym lang = "word set"

(* language density function as defined in ch 3.2 *)
fun dens :: "lang \<Rightarrow> nat \<Rightarrow> nat" where
  "dens L x = card {w \<in> L. nat_of_num w \<le> x}"

(* "density of a word" for convenience *)
fun dens' :: "lang \<Rightarrow> word \<Rightarrow> nat" where
  "dens' L v = dens L (nat_of_num v)"

lemma vim_le:
  fixes x :: nat
  shows "{w. f w \<le> x} = f -` {0..x}"
  by fastforce

lemma vim_le2:
  fixes x :: nat
  shows "{w \<in> A. f w \<le> x} = A \<inter> f -` {0..x}"
  using vim_le[of f x] by blast

(* definition of dens is equivalent to using preimage of gn intersected with L *)
lemma dens_eq_card_vim_gn: "dens L x = card (L \<inter> nat_of_num -` {0..x})"
  using dens.simps[of L x] unfolding vim_le2[of L nat_of_num x] .

lemma lemma4_1: "dens L x \<le> x"
proof (rule ccontr)
  assume "\<not> dens L x \<le> x"

  then have "card {w\<in>L. nat_of_num w \<le> x} \<ge> Suc x" by force
  then obtain W where "W \<subseteq> {w\<in>L. nat_of_num w \<le> x}" and Wcard: "card W = Suc x"
    by (rule obtain_subset_with_card_n)

  then have "nat_of_num ` W \<subseteq> {0<..x}" using nat_of_num_pos by auto
  then have "card (nat_of_num ` W) \<le> x" using card_mono card_greaterThanAtMost
    by (metis diff_zero finite_greaterThanAtMost)
  then show False using Wcard pigeonhole
    by (metis num_eq_iff inj_on_def le_imp_less_Suc)
qed

lemma set_un_le: (* currently unused *)
  fixes x :: nat and P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> nat"
  shows set_un_le_lt_eq: "{w. P w \<and> f w \<le> x} = {w. P w \<and> f w < x} \<union> {w. P w \<and> f w = x}"
    and set_un_le_Suc: "{w. P w \<and> f w \<le> (Suc x)} = {w. P w \<and> f w \<le> x} \<union> {w. P w \<and> f w = (Suc x)}"
  by auto


lemma bounded_lang_finite: "finite {w \<in> L. nat_of_num w \<le> x}"
proof -
  from nat_of_num_inj have "finite (nat_of_num -` {0..x})"
    using finite_vimageI[of "{0..x}" nat_of_num] by blast
  then have "finite (L \<inter> (nat_of_num -` {0..x}))" by blast
  then show "finite {w \<in> L. nat_of_num w \<le> x}" by (fold vim_le2[of L nat_of_num x])
qed

lemma dens_mono: "L \<subseteq> M \<Longrightarrow> dens L x \<le> dens M x"
proof -
  assume "L \<subseteq> M"
  hence "{w \<in> L. nat_of_num w \<le> x} \<subseteq> {w \<in> M. nat_of_num w \<le> x}" by blast
  thus "dens L x \<le> dens M x"
    using card_mono bounded_lang_finite [of M x] by simp
qed

lemma dens_intersect_le: "dens (L1 \<inter> L2) x \<le> dens L1 x"
  using dens_mono by blast

end
