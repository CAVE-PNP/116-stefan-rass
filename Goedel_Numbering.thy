section\<open>Gödel Numbering\<close>

theory Goedel_Numbering
  imports Binary
begin

class goedel_numbering =
  fixes gn :: "'a list \<Rightarrow> nat"
  assumes inj_gn: "inj gn"


instantiation bool :: goedel_numbering
begin
definition gn_bool :: "bool list \<Rightarrow> nat"
  where "gn w = nat_of_bin (w @ [True])"

instance
proof intro_classes
  have gn_comp: "nat_of_bin \<circ> (\<lambda>w. w @ [True]) = gn" unfolding gn_bool_def by force
  have range_appT: "range (\<lambda>w. w @ [True]) = {w. ends_in True w}" by fast

  have "inj_on nat_of_bin (range (\<lambda>w. w @ [True]))" unfolding range_appT by (rule inj_on_nat_of_bin)
  then have "inj (nat_of_bin \<circ> (\<lambda>w. w @ [True]))" using inj_append_L by (subst comp_inj_on_iff[symmetric])
  then show "inj (gn::bool list \<Rightarrow> nat)" unfolding gn_comp .
qed

end


type_synonym word = "bin"


text\<open>Definition of Gödel numbers, given in @{cite \<open>ch.~3.1\<close> rassOwf2017}:

 ``[A Gödel numbering] is a mapping \<open>gn : \<Sigma>\<^sup>* \<rightarrow> \<nat>\<close> that is computable, injective,
  and such that \<open>gn(\<Sigma>\<^sup>*)\<close> is decidable and \<open>gn\<^sup>-\<^sup>1(n)\<close> is computable for all \<open>n \<in> \<nat>\<close> [...].
  The simple choice of \<open>gn(w) = (w)\<^sub>2\<close> is obviously not injective
  (since \<open>(0\<^sup>nw)\<^sub>2 = (w)\<^sub>2\<close> for all \<open>n \<in> \<nat>\<close> and all \<open>w \<in> \<Sigma>\<^sup>*\<close>), but this can be fixed
  conditional on \<open>0 \<notin> \<nat>\<close> by setting \<open>gn(w) := (1w)\<^sub>2\<close>.''\<close>

definition gn :: "word \<Rightarrow> nat" where "gn w = nat_of_bin (w @ [True])"

definition gn_inv :: "nat \<Rightarrow> word" where "gn_inv n = butlast (bin_of_nat n)"

abbreviation (input) is_gn :: "nat \<Rightarrow> bool" where "is_gn n \<equiv> n > 0"

lemmas gn_defs[simp] = gn_def gn_inv_def


subsection\<open>Basic Properties\<close>

lemma gn_gt_0: "gn w > 0" unfolding gn_def by (fold bin_of_nat_end_True) simp

corollary gn_inv_id [simp]: "gn_inv (gn (x)) = x" by simp

corollary inv_gn_id [simp]: "is_gn n \<Longrightarrow> gn (gn_inv n) = n"
proof -
  assume "n > 0"
  with exE bin_of_nat_gt_0_end_True obtain w where w_def: "bin_of_nat n = w @ [True]" .
  show "gn (gn_inv n) = n" unfolding gn_defs w_def butlast_snoc by (fold w_def) (rule nat_bin_nat)
qed

corollary ex_gn: "is_gn n \<Longrightarrow> \<exists>w. gn w = n" using inv_gn_id by blast


subsection\<open>Injectivity and Bijectivity\<close>

lemma inj_gn: "inj gn"
proof -
  have gn_comp: "nat_of_bin \<circ> (\<lambda>w. w @ [True]) = gn" unfolding gn_def by force
  have range_appT: "range (\<lambda>w. w @ [True]) = {w. ends_in True w}" by fast

  have "inj_on nat_of_bin (range (\<lambda>w. w @ [True]))" unfolding range_appT by (rule inj_on_nat_of_bin)
  then have "inj (nat_of_bin \<circ> (\<lambda>w. w @ [True]))" using inj_append_L by (subst comp_inj_on_iff[symmetric])
  then show "inj gn" unfolding gn_comp .
qed

lemma range_gn: "range gn = {0<..}"
proof safe (* intro subset_antisym subsetI, unfold greaterThan_iff, elim imageE forw_subst *)
  fix w show "gn w > 0" by (rule gn_gt_0)
next
  fix n::nat assume "n > 0"
  then have "n = gn (gn_inv n)" by (rule inv_gn_id[symmetric])
  then show "n \<in> range gn" by (intro image_eqI) blast+
qed

text\<open>``[\<^const>\<open>gn\<close>] is a computable bijection between \<open>\<nat>\<close> and \<open>\<Sigma>\<^sup>*\<close>.''\<close>

corollary gn_bij: "bij_betw gn UNIV {0<..}" using inj_gn range_gn by (intro bij_betw_imageI) blast+


lemma gn_inv_inj: "inj_on gn_inv {0<..}"
proof (intro inj_on_inverseI)
  fix x::nat assume "x \<in> {0<..}"
  then have "is_gn x" unfolding greaterThan_iff .
  with inv_gn_id show "gn (gn_inv x) = x" .
qed


subsection\<open>Relation to \<^typ>\<open>num\<close>\<close>

fun num_of_word :: "word \<Rightarrow> num" where
  "num_of_word Nil = num.One" |
  "num_of_word (True # t) = num.Bit1 (num_of_word t)" |
  "num_of_word (False # t) = num.Bit0 (num_of_word t)"

fun word_of_num :: "num \<Rightarrow> word" where
  "word_of_num num.One = Nil" |
  "word_of_num (num.Bit1 t) = True # (word_of_num t)" |
  "word_of_num (num.Bit0 t) = False # (word_of_num t)"


lemma word_num_word_id [simp]: "word_of_num (num_of_word x) = x"
proof (induction x)
  case (Cons a x) thus ?case by (induction a) simp_all
qed \<comment> \<open>case \<open>x = []\<close> by\<close> simp

lemma num_word_num_id [simp]: "num_of_word (word_of_num x) = x"
  by (induction x) auto

corollary num_word_inv:
  shows num_of_word_inv: "inv num_of_word = word_of_num"
    and word_of_num_inv: "inv word_of_num = num_of_word"
  by (simp_all add: inv_equality)

corollary num_word_bij:
  shows num_of_word_bij: "bij num_of_word"
    and word_of_num_bij: "bij word_of_num"
proof -
  show "bij num_of_word" by (intro o_bij[of word_of_num]) auto
  with bij_imp_bij_inv[of num_of_word] show "bij word_of_num" unfolding num_of_word_inv .
qed


lemma gn_altdef: "gn w = nat_of_num (num_of_word w)" by (induction w) auto

lemma bin_of_gn[simp]: "bin_of_nat (gn w) = w @ [True]" by force

lemma gn_inv_of_bin[simp]: "is_gn n \<Longrightarrow> gn_inv n @ [True] = bin_of_nat n"
proof -
  assume "n > 0"
  then have "ends_in True (bin_of_nat n)" by (rule bin_of_nat_gt_0_end_True)
  then obtain w where w: "bin_of_nat n = w @ [True]" ..
  show "gn_inv n @ [True] = bin_of_nat n" unfolding gn_inv_def w butlast_snoc ..
qed

lemma len_gn[simp]: "bit_length (gn w) = length w + 1" by force

lemma len_gn_inv[simp]: "length (gn_inv n) = length (bin_of_nat n) - 1" by force


end
