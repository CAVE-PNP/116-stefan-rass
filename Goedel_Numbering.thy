section\<open>Gödel Numbering\<close>

theory Goedel_Numbering
  imports ExtBinary "Supplementary/Lists"
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

class goedel_numbering' =
  fixes gn' :: "'a list \<Rightarrow> nat" and wf_cond :: "'a list \<Rightarrow> bool"
  assumes bij_gn': "bij_betw gn' {w. wf_cond w} {n. n > 0}"

(*typedef extbool = "{w::bool list. length w = 2}"
proof
  show "[False, False] \<in> {w. length w = 2}" by simp
qed

instantiation extbool :: goedel_numbering
begin
definition gn_extbool :: "extbool list \<Rightarrow> nat"
  where "gn w = nat_of_bin' ([True] # (map Rep_extbool w))"

instance
proof
  have gn_comp: "nat_of_bin' \<circ> (\<lambda>w. ([True] # map Rep_extbool w)) = gn"
    unfolding gn_extbool_def by force
  have range_appT: "range (\<lambda>w. ([True] # map Rep_extbool w)) =
                    {w. starts_with [True] w \<and> set w \<subseteq> {[True], [False]}}"
  proof auto
    fix w and x
    assume "Rep_extbool x \<noteq> [True]"
    thus "Rep_extbool x = [False]" using Rep_extbool by blast
  next
    fix ys
    assume "set ys \<subseteq> {[True], [False]}"
    hence "map Rep_extbool (map Abs_extbool ys) = ys" apply auto
      by (simp add: Abs_extbool_inverse map_idI subset_iff)
    hence "\<exists>w. ys @ [[True]] = (\<lambda>w. map Rep_extbool w @ [[True]]) w" apply auto
      by (metis \<open>map Rep_extbool (map Abs_extbool ys) = ys\<close>)
    thus "[True] # ys \<in> range (\<lambda>w. [True] # map Rep_extbool w)" by auto
  qed
  have "inj_on nat_of_bin' (range (\<lambda>w. [True] # map Rep_extbool w))"
    unfolding range_appT using inj_on_nat_of_bin' sorry
  hence "inj (nat_of_bin' \<circ> (\<lambda>w. [True] # map Rep_extbool w))"
  proof -
    assume "inj_on nat_of_bin' (range (\<lambda>w. [True] # map Rep_extbool w))"
    moreover have "inj (\<lambda>w. [True] # (map Rep_extbool w))"
      by (simp add: Rep_extbool_inject inj_altdef)
    ultimately show "inj (nat_of_bin' \<circ> (\<lambda>w. [True] # map Rep_extbool w))"
      using comp_inj_on by auto
  qed
  thus "inj (gn :: extbool list \<Rightarrow> nat)" unfolding gn_comp[symmetric] .
qed
end*)

type_synonym word = "bin"

type_synonym word' = "bin'"


text\<open>Definition of Gödel numbers, given in @{cite \<open>ch.~3.1\<close> rassOwf2017}:

 ``[A Gödel numbering] is a mapping \<open>gn : \<Sigma>\<^sup>* \<rightarrow> \<nat>\<close> that is computable, injective,
  and such that \<open>gn(\<Sigma>\<^sup>*)\<close> is decidable and \<open>gn\<^sup>-\<^sup>1(n)\<close> is computable for all \<open>n \<in> \<nat>\<close> [...].
  The simple choice of \<open>gn(w) = (w)\<^sub>2\<close> is obviously not injective
  (since \<open>(0\<^sup>nw)\<^sub>2 = (w)\<^sub>2\<close> for all \<open>n \<in> \<nat>\<close> and all \<open>w \<in> \<Sigma>\<^sup>*\<close>), but this can be fixed
  conditional on \<open>0 \<notin> \<nat>\<close> by setting \<open>gn(w) := (1w)\<^sub>2\<close>.''\<close>

definition gn :: "word \<Rightarrow> nat" where "gn w = nat_of_bin (w @ [True])"

definition gn_inv :: "nat \<Rightarrow> word" where "gn_inv n = butlast (bin_of_nat n)"

abbreviation (input) is_gn :: "nat \<Rightarrow> bool" where "is_gn n \<equiv> n > 0"

lemmas gn_defs = gn_def gn_inv_def


subsection\<open>Basic Properties\<close>

lemma gn_gt_0[simp, intro]: "gn w > 0" unfolding gn_def by simp

corollary gn_inv_id [simp]: "gn_inv (gn (x)) = x" unfolding gn_defs by simp

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


lemma gn_altdef: "gn w = nat_of_num (num_of_word w)" by (induction w) (auto simp add: gn_def)

lemma bin_of_gn[simp]: "bin_of_nat (gn w) = w @ [True]" by (simp add: gn_def)

lemma gn_inv_of_bin[simp]: "is_gn n \<Longrightarrow> gn_inv n @ [True] = bin_of_nat n"
proof -
  assume "n > 0"
  then have "ends_in True (bin_of_nat n)" by (rule bin_of_nat_gt_0_end_True)
  then obtain w where w: "bin_of_nat n = w @ [True]" ..
  show "gn_inv n @ [True] = bin_of_nat n" unfolding gn_inv_def w butlast_snoc ..
qed

lemma len_gn[simp]: "bit_length (gn w) = length w + 1" by force

lemma len_gn_inv[simp]: "length (gn_inv n) = length (bin_of_nat n) - 1" by (simp add: gn_inv_def)

lemma gn_inv_app_ends_in_True: "b' = r@[True] \<Longrightarrow> gn_inv (b@b')\<^sub>2 = b@butlast (b')"
  apply (induction b')
   apply auto
  by (metis append_eq_appendI bin_nat_bin butlast_snoc gn_inv_def)

lemma gn_length_mono: "gn x \<le> gn y \<Longrightarrow> length x \<le> length y"
  unfolding gn_def apply (induction x arbitrary: y)
   apply auto
  by (metis ExtBinary.lengths_le Suc_le_mono append_Cons bin_nat_bin length_Suc_conv
      length_append_singleton nat_of_bin.simps(2))

lemma length_gn_mono: "length x < length y \<Longrightarrow> gn x < gn y"
  unfolding gn_def apply (induction x arbitrary: y)
   apply auto
    apply (metis Binary.inc.simps(1) Suc_lessI append_self_conv2 bin_nat_bin
      bin_of_nat.simps(1) bin_of_nat.simps(2) nat_of_bin_gt_0_end_True)
   apply (metis (mono_tags, opaque_lifting) Suc_eq_plus1_left Suc_less_eq
      length_Cons length_append_singleton nat_of_bin.simps(2) nat_of_bin_len_mono)
  by (metis Suc_eq_plus1 Suc_less_eq2 bin_nat_bin bit_len_double
      length_append_singleton nat_bin_nat nat_of_bin_gt_0_end_True
      nat_of_bin_len_mono)

function bij_bin_bin' :: "bin \<Rightarrow> bin'" where
  "bij_bin_bin' (t@[False]) = [False, False]#bij_bin_bin' t" |
  "bij_bin_bin' (t@[True]) = bin'_of_bin (t@[True])" |
  "bij_bin_bin' [] = []"
        apply auto
  apply (erule rev_cases)
  by blast
termination by lexicographic_order

lemma bij_bin_bin'_wf [intro]: "bin'_wf (bij_bin_bin' xs)"
proof (induction xs rule: bij_bin_bin'.induct)
  case (1 t)
  then show ?case by fastforce
next
  case (2 t)
  then show ?case by auto
next
  case 3
  then show ?case by simp
qed

lemma nat_of_bin'_bij_bin_bin' [simp]: "nat_of_bin' (bij_bin_bin' xs) = nat_of_bin xs"
proof (induction xs rule: bij_bin_bin'.induct)
  case (1 t)
  then show ?case by (simp add: nat_of_bin_app)
next
  case (2 t)
  then show ?case using bij_bin_bin'.simps(2) nat_of_bin_via_bin' by presburger
next
  case 3
  then show ?case by simp
qed

function bij_bin'_bin :: "bin' \<Rightarrow> bin" where
  "bij_bin'_bin [] = []" |
  "bij_bin'_bin ([False, False]#t) = (bij_bin'_bin t)@[False]" |
  "bij_bin'_bin ([]#t) = bin_of_bin' t" |
  "bij_bin'_bin ([b]#t) = bin_of_bin' ([b]#t)" |
  "bij_bin'_bin ([True, False]#t) = bin_of_bin' ([True, False]#t)" |
  "bij_bin'_bin ([False, True]#t) = bin_of_bin' ([False, True]#t)" |
  "bij_bin'_bin ([True, True]#t) = bin_of_bin' ([True, True]#t)" |
  "bij_bin'_bin ((b1#b2#b3#t')#t) = bin_of_bin' ((b1#b2#b3#t')#t)"
                      apply auto
  apply (erule list.exhaust)
  apply simp
  by (metis (full_types) list.exhaust)
termination by lexicographic_order

lemma bij_bin_bin'_is_bij: "bij_betw bij_bin_bin' UNIV {w. bin'_wf w}"
proof -
  have "bij_bin_bin' x = bij_bin_bin' y \<Longrightarrow> x = y" for x y :: bin
  proof (induction x arbitrary: y rule: bij_bin_bin'.induct)
    case (1 t)
    then show ?case apply simp
      by (metis bij_bin_bin'.elims in_set_replicate list.distinct(1) list.sel(3)
          list.size(3) set_ConsD starts_with_True.simps(2) starts_with_True_bin'_bin
          trim_nil trim_nil_eq)
  next
    case (2 t)
    then show ?case
      by (metis Binary.inc.simps(1) bij_bin_bin'.elims bij_bin_bin'.simps(2)
          bin'_of_bin_eq1 in_set_replicate length_Cons length_inc_Suc_iff
          length_replicate list.size(3) list.size(3) set_ConsD
          starts_with_True.simps(1) starts_with_True.simps(2)
          starts_with_True_bin'_bin)
  next
    case 3
    then show ?case
      by (metis ExtBinary.bin_of_bin'.simps bij_bin_bin'.elims bij_bin_bin'.simps(3)
            bin'_of_bin_eq1 bin_nat_bin_drop_zs bin_of_nat.simps(1) flatten.simps(1)
            list.discI nat_of_bin.simps(1) rev.simps(1))
  qed
  hence "inj bij_bin_bin'" by (rule injI)
  moreover have "bin'_wf x \<Longrightarrow> bij_bin_bin' (bij_bin'_bin x) = x" for x :: bin'
    apply (induction x rule: bij_bin'_bin.induct)
           apply auto
    using bin'_wf_ConsD apply blast
                 apply (simp_all add: bin'_wf_def)
  proof -
    fix t :: bin'
    assume a1: "\<forall>bit\<in>set t. length bit = 2"
    have 1: "bij_bin_bin' (rev (flatten t) @ [False, True]) =
             bin'_of_bin (rev (flatten t) @ [False, True])"
      by (metis append.assoc append_Cons append_Nil bij_bin_bin'.simps(2))
    show "bij_bin_bin' (rev (flatten t) @ [False, True]) = [True, False] # t"
      unfolding 1 by (simp add: a1 bin'_wf_def even_group_2_Cons2)
    show "group_2 False (True # flatten t) = [False, True] # t"
      by (simp add: a1 bin'_wf_def even_group_2_Cons1)
    have 2: "bij_bin_bin' (rev (flatten t) @ [True, True]) =
             bin'_of_bin (rev (flatten t) @ [True, True])"
      by (metis append.assoc append_Cons append_Nil bij_bin_bin'.simps(2))
    show "bij_bin_bin' (rev (flatten t) @ [True, True]) = [True, True] # t"
      unfolding 2 by (simp add: a1 bin'_wf_def even_group_2_Cons2)
  qed
  ultimately show "bij_betw bij_bin_bin' UNIV {w. bin'_wf w}"
    unfolding bij_betw_def by auto (metis rangeI)
qed

lemma nat_of_bin_bij_bin'_bin [simp]: "nat_of_bin (bij_bin'_bin xs) = nat_of_bin' xs"
proof (induction xs rule: bij_bin'_bin.induct)
  case 1
  then show ?case by simp
next
  case (2 t)
  then show ?case
    using ExtBinary.nat_of_bin'_app0 bij_bin'_bin.simps(2)
      nat_of_bin_app0 by presburger
next
  case (3 t)
  then show ?case by simp
next
  case (4 b t)
  then show ?case by simp
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
  then show ?case by simp
qed

lemma nat_of_bin_bij_bin'_bin_eq_0_iff: "nat_of_bin (bij_bin'_bin xs) = 0 \<longleftrightarrow>
                                         nat_of_bin' xs = 0"
  by simp

lemma set_bij_bin'_bin_iff: "set (bij_bin'_bin xs) \<subseteq> {False} \<longleftrightarrow>
                             set (flatten xs) \<subseteq> {False}"
  by (meson nat_of_bin'_eq_0_iff nat_of_bin_bij_bin'_bin_eq_0_iff nat_of_bin_eq_0_iff)

lemma bij_bin_bin'_is_bij2: "bij_betw bij_bin_bin' {w. True \<in> set w}
                             {w. bin'_wf w \<and> True \<in> set (flatten w)}"
proof -
  have "inj_on bij_bin_bin' {w. True \<in> set w}"
    using bij_betw_def bij_bin_bin'_is_bij by blast
  moreover have "image bij_bin_bin' {w. True \<in> set w} =
                 {w. bin'_wf w \<and> True \<in> set (flatten w)}"
  proof -
    have 1: "True \<in> set w \<Longrightarrow> True \<in> set (flatten (bij_bin_bin' w))" for w :: bin
      by (metis (mono_tags, opaque_lifting) empty_iff insert_iff
          nat_of_bin'_bij_bin_bin' nat_of_bin'_eq_0_iff nat_of_bin_eq_0_iff
          subset_code(1))
    have 2: "\<And>x. bin'_wf x \<Longrightarrow> True \<in> set (flatten x) \<Longrightarrow>
             True \<in> set (bij_bin'_bin x)"
      by (smt (verit, ccfv_SIG) nat_of_bin'_eq_0_iff nat_of_bin_bij_bin'_bin
          nat_of_bin_eq_0_iff singleton_iff subsetD subsetI)
    have 3: "bin'_wf x \<Longrightarrow> True \<in> set (flatten x) \<Longrightarrow>
             x = bij_bin_bin' (bij_bin'_bin x)" for x :: bin'
    proof (induction x rule: bij_bin'_bin.induct)
      case 1
      then show ?case by simp
    next
      case (2 t)
      then show ?case by fastforce
    next
      case (3 t)
      then show ?case by fastforce
    next
      case (4 b t)
      then show ?case by fastforce
    next
      case (5 t)
      then show ?case
      proof simp
        obtain b :: bin where b_def: "rev (flatten t) @ [False, True] = b @ [True]"
          by simp
        show "[True, False] # t = bij_bin_bin' (rev (flatten t) @ [False, True])"
          unfolding b_def apply simp
          by (metis "5.prems"(1) b_def flatten.simps(2) group_2_flatten_id
              rev.simps(2) rev_append rev_rev_ident)
      qed
    next
      case (6 t)
      then show ?case apply simp
        by (metis bin'_wf_ConsD bin'_wf_even even_group_2_Cons1 group_2_flatten_id)
    next
      case (7 t)
      then show ?case
      proof simp
        obtain b :: bin where b_def: "rev (flatten t) @ [True, True] = b @ [True]"
          by simp
        show "[True, True] # t = bij_bin_bin' (rev (flatten t) @ [True, True])"
          unfolding b_def apply simp
          by (metis "7.prems"(1) b_def flatten.simps(2) group_2_flatten_id
              rev.simps(2) rev_append rev_rev_ident)
      qed
    next
      case (8 b1 b2 b3 t' t)
      then show ?case by (simp add: bin'_wf_def)
    qed
    show "bij_bin_bin' ` {w. True \<in> set w} =
                     {w. bin'_wf w \<and> True \<in> set (flatten w)}"
      unfolding image_def apply auto
       apply (erule 1)
      using 2 3 by auto
  qed
  ultimately show ?thesis by (simp add: bij_betw_def)
qed

lemma nat_of_bin_gt_0_iff: "nat_of_bin w > 0 \<longleftrightarrow> True \<in> set w"
  by (metis (full_types) in_mono nat_of_bin_eq_0_iff not_gr0 replicate_length_same
      replicate_set_eq singletonD)

lemma nat_of_bin'_gt_0_iff: "nat_of_bin' w > 0 \<longleftrightarrow> True \<in> set (flatten w)"
  by (simp add: nat_of_bin_gt_0_iff)

lemma bij_bin_bin'_bin [simp]: "bin'_wf w \<Longrightarrow> bij_bin_bin' (bij_bin'_bin w) = w"
proof (induction w rule: bij_bin'_bin.induct)
  case 1
  then show ?case by simp
next
  case (2 t)
  have 1: "bin'_wf t" by (rule 2(2) [THEN bin'_wf_ConsD])
  show ?case unfolding bij_bin'_bin.simps(2) bij_bin_bin'.simps(1) 2(1) [OF 1] ..
next
  case (3 t)
  then show ?case by fastforce
next
  case (4 b t)
  then show ?case by fastforce
next
  case (5 t)
  then show ?case
  proof simp
    obtain b :: bin where b_def: "rev (flatten t) @ [False, True] = b @ [True]"
      by simp
    show "bij_bin_bin' (rev (flatten t) @ [False, True]) = [True, False] # t"
      unfolding b_def apply simp
      by (metis 5 b_def flatten.simps(2) group_2_flatten_id rev.simps(2)
          rev_append rev_rev_ident)
  qed
next
  case (6 t)
  then show ?case apply simp
    by (metis bin'_wf_ConsD bin'_wf_even even_group_2_Cons1 group_2_flatten_id)
next
  case (7 t)
  then show ?case
  proof simp
    obtain b :: bin where b_def: "rev (flatten t) @ [True, True] = b @ [True]" by simp
    show "bij_bin_bin' (rev (flatten t) @ [True, True]) = [True, True] # t"
      unfolding b_def apply simp
      by (metis 7 b_def flatten.simps(2) group_2_flatten_id rev.simps(2)
          rev_append rev_rev_ident)
  qed
next
  case (8 b1 b2 b3 t' t)
  then show ?case by (simp add: bin'_wf_def)
qed

lemma bij_bin'_bin_bin' [simp]: "bij_bin'_bin (bij_bin_bin' w) = w"
proof (induction w rule: bij_bin_bin'.induct)
  case (1 t)
  then show ?case by simp
next
  case (2 t)
  then show ?case
  proof simp
    show "bij_bin'_bin (group_2 False (True # rev t)) = t @ [True]"
    proof (cases "group_2 False (True # rev t)" rule: bij_bin'_bin.cases)
      case 1
      then show ?thesis by simp
    next
      case (2 t)
      then show ?thesis
        by (metis list.distinct(1) list.sel(1) nat_of_bin.simps(1)
            nat_of_bin_eq_0_iff set_ConsD singletonD starts_with_True.simps(2)
            starts_with_True_group_2 subset_code(1))
    next
      case (3 t)
      then show ?thesis
        by (metis bin'_wf_ConsD flatten.simps(2) group_2_bin'_wf group_2_flatten_id
            not_Cons_self2 self_append_conv2)
    next
      case (4 b t)
      then show ?thesis
        by (metis bin'_wfE distinct_adj_Cons distinct_adj_Cons_Cons group_2_bin'_wf
            list.inject list.set_intros(1))
    next
      case (5 t)
      then show ?thesis
        by (metis ExtBinary.bin'_of_bin.simps ExtBinary.bin_of_bin'.simps
            ExtBinary.nat_of_bin'.elims bij_bin'_bin.simps(5) bin_nat_bin
            bin_nat_bin_drop_zs nat_of_bin_dropWhile nat_of_bin_via_bin'
            rev.simps(2) rev_rev_ident)
    next
      case (6 t)
      then show ?thesis apply simp
        by (metis even_Suc even_group_2_Cons1 flatten.simps(2)
            flatten_group_2_even hd_append2 length_Cons list.distinct(1)
            list.sel(1) list.sel(3) rev_swap)
    next
      case (7 t)
      then show ?thesis apply simp
        by (smt (z3) Nitpick.size_list_simp(2) even_Suc even_group_2_Cons1
            flatten_group_2_even length_greater_0_conv list.collapse list.sel(1)
            list.sel(3) odd_group_2_Cons1 odd_pos rev_eq_Cons_iff)
    next
      case (8 b1 b2 b3 t' t)
      then show ?thesis
        by (metis ExtBinary.bin'_of_bin.simps bij_bin'_bin.simps(8) bin'_of_bin_eq1
            rev.simps(2) rev_rev_ident)
    qed
  qed
next
  case 3
  then show ?case by simp
qed

lemma bij_bin'_bin_is_bij: "bij_betw bij_bin'_bin {w. bin'_wf w} UNIV"
  by (metis UNIV_I bij_betw_cong bij_betw_inv_into bij_betw_inv_into_left
      bij_bin_bin'_bin bij_bin_bin'_is_bij mem_Collect_eq)

definition gn' :: "word' \<Rightarrow> nat" where "gn' w \<equiv> gn (bij_bin'_bin w)"

definition gn'_inv :: "nat \<Rightarrow> word'"
  where "gn'_inv n = bij_bin_bin' (gn_inv n)"

abbreviation (input) is_gn' :: "nat \<Rightarrow> bool" where "is_gn' n \<equiv> n > 0"

lemmas gn'_defs = gn'_def gn'_inv_def

subsection\<open>Basic Properties\<close>

lemma gn'_gt_0[simp, intro]: "gn' w > 0" unfolding gn'_def by simp

corollary gn'_inv_id [simp]: "bin'_wf x \<Longrightarrow> gn'_inv (gn' x) = x"
  unfolding gn'_defs by simp

corollary inv_gn'_id [simp]: "is_gn' n \<Longrightarrow> gn' (gn'_inv n) = n"
  unfolding gn'_defs by simp

corollary ex_gn': "is_gn' n \<Longrightarrow> \<exists>w. gn' w = n" using inv_gn'_id by blast

corollary ex_gn'_bin'_wf: "is_gn' n \<Longrightarrow> \<exists>w. bin'_wf w \<and> gn' w = n"
  using gn'_defs(2) inv_gn'_id by auto


subsection\<open>Injectivity and Bijectivity\<close>
lemma gn'_inj_on: "inj_on gn' {w. bin'_wf w}"
  by (metis gn'_inv_id inj_on_inverseI mem_Collect_eq)

(*lemma range_gn': "range gn' = {0<..}"
proof safe (* intro subset_antisym subsetI, unfold greaterThan_iff, elim imageE forw_subst *)
  fix w show "gn' w > 0" by (rule gn'_gt_0)
next
  fix n::nat assume "n > 0"
  then have "n = gn' (gn'_inv n)" by (rule inv_gn'_id[symmetric])
  then show "n \<in> range gn'" by (intro image_eqI) blast+
qed*)

text\<open>``[\<^const>\<open>gn'\<close>] is a computable bijection between \<open>\<nat>\<close> and \<open>\<Sigma>\<^sup>*\<close>.''\<close>

lemma nat_of_bin'_inc' [simp]: "nat_of_bin' ((inc' ^^ n) []) = n"
  apply (induction n)
   apply auto
  by (metis inc_Suc nat_of_bin_dropWhile nat_of_bin_trim)

lemma nat_of_bin'_exists: obtains w :: "bool list list" where "nat_of_bin' w = n"
  using nat_of_bin'_inc' by blast

lemma bin'_of_nat_range_subset: "x \<in> range bin'_of_nat \<Longrightarrow> bin'_wf x"
  by auto

corollary gn'_bij: "bij_betw gn' {w. bin'_wf w} {0<..}"
  unfolding gn'_def
  by (smt (verit, del_insts) bij_betwI' bij_betw_iff_bijections bij_bin'_bin_bin'
      bij_bin_bin'_is_bij gn_bij)

lemma gn'_inv_inj: "inj_on gn'_inv {0<..}"
proof (intro inj_on_inverseI)
  fix x::nat assume "x \<in> {0<..}"
  then have "is_gn' x" unfolding greaterThan_iff .
  with inv_gn'_id show "gn' (gn'_inv x) = x" .
qed

lemma in_range_gn'_iff_gt_0: "n \<in> range gn' \<longleftrightarrow> n > 0"
  using ex_gn' by auto

lemma in_im_gn'_bin'_iff_gt_0: "n \<in> gn' ` {w. bin'_wf w} \<longleftrightarrow> n > 0"
  by (auto dest: ex_gn'_bin'_wf)

corollary gn'_inv_bij: "bij_betw gn'_inv {0<..} {w. bin'_wf w}"
  unfolding bij_betw_def
proof auto
  show "inj_on gn'_inv {0<..}" by (rule gn'_inv_inj)
  show "n > 0 \<Longrightarrow> bin'_wf (gn'_inv n)" for n :: nat
    using gn'_defs(2) by auto
  show "bin'_wf w \<Longrightarrow> w \<in> gn'_inv ` {0<..}" for w :: "bool list list"
    by (metis gn'_defs(1) gn'_inv_id image_iff range_eqI range_gn)
qed

subsection\<open>Relation to \<^typ>\<open>num\<close>\<close>

fun num_of_word' :: "word' \<Rightarrow> num" where
  "num_of_word' w = num_of_word (bij_bin'_bin w)"

fun word'_of_num :: "num \<Rightarrow> word'" where
  "word'_of_num n = bij_bin_bin' (word_of_num n)"

lemma word'_num_word'_id [simp]: "bin'_wf x \<Longrightarrow>
                                  word'_of_num (num_of_word' x) = x"
  by simp

lemma num_word'_num_id [simp]: "num_of_word' (word'_of_num x) = x"
  by simp

corollary num_word'_bij:
  shows num_of_word'_bij: "bij_betw num_of_word' {w. bin'_wf w} UNIV"
    and word'_of_num_bij: "bij_betw word'_of_num UNIV {w. bin'_wf w}"
proof -
  have "inj_on num_of_word' {w. bin'_wf w}"
    by (metis inj_on_inverseI mem_Collect_eq word'_num_word'_id)
  moreover have "\<exists>x. y = num_of_word' x" for y
    by (rule exI) (rule num_word'_num_id [symmetric])
  ultimately show "bij_betw num_of_word' {w. bin'_wf w} UNIV"
    by (metis (no_types, opaque_lifting) UNIV_I UNIV_eq_I bij_betwE
        bij_bin'_bin_bin' bij_bin_bin'_is_bij inj_on_imp_bij_betw num_of_word'.simps)
  moreover have "inj word'_of_num" by (meson inj_on_inverseI num_word'_num_id)
  moreover have "bin'_wf y \<Longrightarrow> \<exists>x. y = word'_of_num x" for y
    by (rule exI) (rule word'_num_word'_id [symmetric])
  ultimately show "bij_betw word'_of_num UNIV {w. bin'_wf w}"
    by (smt (verit, ccfv_threshold) bij_betw_iff_bijections
        mem_Collect_eq num_word'_num_id)
qed

lemma gn'_altdef: "gn' w = nat_of_num (num_of_word' w)"
  apply (simp add: gn'_defs)
  using gn_altdef by blast

(*lemma bin'_of_gn'[simp]:
  fixes w :: "bool list list"
  assumes "bin'_wf w"
  shows "bin'_of_nat (gn' w) = bij_bin_bin' (flatten w@[True])"
  unfolding gn'_def
proof simp
  have 1: "even (length (rev (flatten w)))" using assms by simp
  show "group_2 False (True # rev (bij_bin'_bin w)) =
        group_2 False (True # rev (flatten w))"
    unfolding even_group_2_Cons1 [OF 1]
    apply (cases "even (length (rev (bij_bin'_bin w)))")
     apply (rule even_group_2_Cons1 [THEN ssubst])
      apply assumption
     apply simp
     apply (induction w rule: bij_bin'_bin.induct)
    apply simp 
qed

lemma gn'_inv_of_bin'[simp]: "is_gn' n \<Longrightarrow> [True] # gn'_inv n = bin'_of_nat n"
proof -
  assume "n > 0"
  then have "starts_with [True] (bin'_of_nat n)" by (rule bin'_of_nat_gt_0_start_True)
  then obtain w where w: "bin'_of_nat n = [True] # w" ..
  show "[True] # gn'_inv n = bin'_of_nat n" unfolding gn'_inv_def w by simp
qed

lemma len_gn'[simp]: "bin'_wf w \<Longrightarrow> bit'_length (gn' w) = length (flatten w) + 1"
  unfolding gn'_altdef apply simp
  apply (induction w rule: bij_bin'_bin.induct)
         apply simp
        apply (frule bin'_wf_ConsD)
        apply auto[1]

lemma len_gn'_inv[simp]: "length (gn'_inv n) = length (bin'_of_nat n) - 1"
  by (simp add: gn'_inv_def)

lemma gn'_lt_le_length: "bin'_wf x \<Longrightarrow> bin'_wf y \<Longrightarrow> gn' x < gn' y \<Longrightarrow>
                         length x \<le> length y"
  unfolding gn'_def apply (induction x arbitrary: y rule: bij_bin'_bin.induct)
         apply simp
        apply (frule bin'_wf_ConsD)
        apply auto[1] *)

lemma gn'_eq_length: "bin'_wf x \<Longrightarrow> bin'_wf y \<Longrightarrow> gn' x = gn' y \<Longrightarrow>
                      length x = length y"
  using gn'_inj_on by (metis gn'_inv_id)

(*lemma length_lt_gn': "length x < length y \<Longrightarrow> gn' x < gn' y"
  by (meson gn'_le_length leD leI) *)

lemma gn'_gt_nat_of_bin': "gn' w > nat_of_bin' w"
  unfolding gn'_def
proof (induction w rule: bij_bin'_bin.induct)
  case 1
  then show ?case by simp
next
  case (2 t)
  then show ?case apply simp
    by (metis butlast_append butlast_snoc le_eq_less_or_eq length_append
        length_append_singleton length_gn_mono less_add_Suc1 order_less_le_trans)
next
  case (3 t)
  then show ?case by (simp add: gn_def nat_of_bin_append1)
next
  case (4 b t)
  then show ?case
    using ExtBinary.nat_of_bin'.simps bij_bin'_bin.simps(4) gn_def
      nat_of_bin_append1 nat_of_bin_max trans_less_add1 by presburger
next
  case (5 t)
  then show ?case apply simp
    using gn_def nat_of_bin_append1 nat_of_bin_max trans_less_add1 by presburger
next
  case (6 t)
  then show ?case using gn_def nat_of_bin_app1 by auto
next
  case (7 t)
  then show ?case apply simp
    using gn_def nat_of_bin_append1 nat_of_bin_max trans_less_add1 by presburger
next
  case (8 b1 b2 b3 t' t)
  then show ?case by (simp add: gn_def nat_of_bin_append1)
qed

lemma length_ends_in_True_mono: "length xs < length ys \<Longrightarrow>
                                 (xs@[True])\<^sub>2 < (ys@[True])\<^sub>2"
  apply (induction xs)
   apply auto
    apply (metis Binary.inc.simps(1) Suc_lessI append_self_conv2
      bin_nat_bin bin_of_nat.simps(1) bin_of_nat.simps(2) nat_of_bin_gt_0_end_True)
proof -
  fix a :: bool and xsa :: "bool list"
  assume "Suc (length xsa) < length ys"
  then have "length (True # xsa @ [True]) < Suc (length ys)"
    by simp
  then show "Suc (2 * (xsa @ [True])\<^sub>2) < (ys @ [True])\<^sub>2"
    by (metis (full_types) length_append_singleton nat_of_bin.simps(2)
        nat_of_bin_len_mono plus_1_eq_Suc)
next
  fix a :: bool and xs :: bin
  show "(xs @ [True])\<^sub>2 < (ys @ [True])\<^sub>2 \<Longrightarrow>
        Suc (length xs) < length ys \<Longrightarrow> \<not> a \<Longrightarrow> 2 * (xs @ [True])\<^sub>2 < (ys @ [True])\<^sub>2"
  proof -
    assume a1: "Suc (length xs) < length ys"
    have "\<forall>bs. Suc (2 * (bs)\<^sub>2) = (True # bs)\<^sub>2"
      by simp
    then show ?thesis
      using a1 by (metis Cons_eq_append_conv Suc_lessD gn_def length_Suc_conv
          length_gn_mono)
  qed
qed

lemma length_bij_bin'_bin_upper_bound: "bin'_wf b' \<Longrightarrow>
                                        length (bij_bin'_bin b') \<le> 2 * length b'"
proof (induction b' rule: bij_bin'_bin.induct)
  case 1
  then show ?case by simp
next
  case (2 t)
  then show ?case by fastforce
next
  case (3 t)
  then show ?case by fastforce
next
  case (4 b t)
  then show ?case by fastforce
next
  case (5 t)
  then show ?case apply simp
    using bin'_wf_ConsD bin'_wf_length less_or_eq_imp_le by blast
next
  case (6 t)
  then show ?case apply simp
    by (metis bin'_wf_ConsD bin'_wf_length suc_is_ge)
next
  case (7 t)
  then show ?case apply simp
    using bin'_wf_ConsD bin'_wf_length le_eq_less_or_eq by blast
next
  case (8 b1 b2 b3 t' t)
  then show ?case by fastforce
qed

lemma length_bij_bin'_bin_lower_bound: "starts_with_True b' \<Longrightarrow> bin'_wf b' \<Longrightarrow>
                                        length (bij_bin'_bin b') \<ge> 2 * length b' - 1"
proof (induction b' rule: bij_bin'_bin.induct)
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
  then show ?case by fastforce
next
  case (5 t)
  then show ?case apply simp
    using bin'_wf_ConsD bin'_wf_length suc_is_ge by blast
next
  case (6 t)
  then show ?case apply simp
    using bin'_wf_ConsD bin'_wf_length by presburger
next
  case (7 t)
  then show ?case by (simp add: bin'_wf_def)
next
  case (8 b1 b2 b3 t' t)
  then show ?case by fastforce
qed

lemma length_bij_bin'_bin_starts_with_TrueX: "starts_with [True, x] b' \<Longrightarrow>
                                              bin'_wf b' \<Longrightarrow>
                                              length (bij_bin'_bin b') =
                                              2 * length b'"
proof (induction b' rule: bij_bin'_bin.induct)
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
  then show ?case by simp
next
  case (5 t)
  then show ?case apply simp
    apply (drule bin'_wf_ConsD)
    by simp
next
  case (6 t)
  then show ?case by simp
next
  case (7 t)
  then show ?case apply simp
    apply (drule bin'_wf_ConsD)
    by simp
next
  case (8 b1 b2 b3 t' t)
  then show ?case by simp
qed

lemma not_starts_with_True_prefix: "\<not>starts_with_True xs \<Longrightarrow> bin'_wf xs \<Longrightarrow>
                                    \<exists>n ys. xs = (replicate n [False, False])@ys"
  apply (induction xs)
   apply auto
  by (metis replicate_0 self_append_conv2)

lemma gn'_length_mono: "starts_with_True x \<Longrightarrow> bin'_wf x \<Longrightarrow> bin'_wf y \<Longrightarrow>
                        gn' x < gn' y \<Longrightarrow> starts_with_True y \<Longrightarrow> length x \<le> length y"
  apply (induction x rule: starts_with_True_induct)
   apply auto
  unfolding gn'_def gn_def
proof -
  fix x y' :: "bool list" and xs :: bin'
  assume a1: "bin'_wf (x # xs) \<Longrightarrow>
              (bij_bin'_bin (x # xs) @ [True])\<^sub>2 < (bij_bin'_bin y @ [True])\<^sub>2 \<Longrightarrow>
              Suc (length xs) \<le> length y" and
         a2: "True \<in> set x" and
         a3: "bin'_wf (x # y' # xs)" and
         a4: "bin'_wf y" and
         a5: "(bij_bin'_bin (x # y' # xs) @ [True])\<^sub>2 < (bij_bin'_bin y @ [True])\<^sub>2" and
         a6: "starts_with_True y"
  have 1: "bin'_wf (x # xs)" using a3 by fastforce
  hence 2: "bin'_wf xs" by fastforce
  obtain a b :: bool where x_def: "x = [a, b]" using 1 by fastforce
  have a_or_b: "a \<or> b" using a2 unfolding x_def by simp
  obtain c d :: bool where y'_def: "y' = [c, d]" using a3 by fastforce
  obtain e f :: bool and t :: bin' where y_def: "y = [e, f]#t"
    using a4 a6
    by (metis bin'_wfE list.exhaust list.set_intros(1) starts_with_True.simps(1))
  have e_or_f: "e \<or> f" using a6 unfolding y_def by simp
  have 3: "(bij_bin'_bin (x # xs) @ [True])\<^sub>2 < (bij_bin'_bin y @ [True])\<^sub>2"
    using a5 unfolding x_def using a_or_b apply auto
     apply (cases b)
      apply auto
    using bin_app_ge dual_order.strict_trans2 apply blast
    using bin_app_ge dual_order.strict_trans2 apply blast
    apply (cases a)
     apply auto
    using bin_app_ge dual_order.strict_trans2 by blast+
  have 4: "Suc (length xs) = length y \<Longrightarrow>
           (bij_bin'_bin (x # y' # xs) @ [True])\<^sub>2 > (bij_bin'_bin y @ [True])\<^sub>2"
    apply (rule length_ends_in_True_mono)
    unfolding x_def using a_or_b apply auto
     apply (cases b)
    apply auto
      apply (metis (no_types, lifting) 1 y'_def a4 add.commute bin'_wf_length
        dual_order.strict_trans2 flatten.simps(2) length_Cons length_append
        length_bij_bin'_bin_upper_bound lessI less_SucI x_def)
     apply (metis (no_types, lifting) 1 y'_def a4 add.commute bin'_wf_length
        dual_order.strict_trans2 flatten.simps(2) length_Cons length_append
        length_bij_bin'_bin_upper_bound lessI less_SucI x_def)
    apply (cases a)
     apply auto
     apply (metis (no_types, lifting) 1 y'_def a4 add.commute bin'_wf_length
        dual_order.strict_trans2 flatten.simps(2) length_Cons length_append
        length_bij_bin'_bin_upper_bound lessI less_SucI x_def)
    by (metis (no_types, lifting) 1 y'_def a4 add.commute bin'_wf_length
        dual_order.strict_trans2 flatten.simps(2) length_Cons length_append
        length_bij_bin'_bin_upper_bound lessI x_def)
  show "Suc (Suc (length xs)) \<le> length y" using a1 [OF 1 3] 4 a5 by linarith
qed

lemma length_bij_bin'_bin_ge: "bin'_wf xs \<Longrightarrow> length (bij_bin'_bin xs) \<ge> length xs"
proof (induction xs rule: bij_bin'_bin.induct)
  case 1
  then show ?case by simp
next
  case (2 t)
  then show ?case by fastforce
next
  case (3 t)
  then show ?case by fastforce
next
  case (4 b t)
  then show ?case by fastforce
next
  case (5 t)
  then show ?case apply simp
    using bin'_wf_ConsD bin'_wf_length by presburger
next
  case (6 t)
  then show ?case apply simp
    using bin'_wf_ConsD bin'_wf_length by presburger
next
  case (7 t)
  then show ?case apply simp
    using bin'_wf_ConsD bin'_wf_length by presburger
next
  case (8 b1 b2 b3 t' t)
  then show ?case by fastforce
qed

lemma length_gn'_ge: "starts_with_True xs \<Longrightarrow> bin'_wf xs \<Longrightarrow>
                      length (bin'_of_nat (gn' xs)) \<ge> length xs"
  unfolding gn'_def
proof (induction xs rule: bij_bin'_bin.induct)
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
  then show ?case by fastforce
next
  case (5 t)
  then show ?case by (simp add: bin'_wf_ConsD)
next
  case (6 t)
  then show ?case apply simp
    apply (drule bin'_wf_ConsD)
    by simp
next
  case (7 t)
  then show ?case apply simp
    apply (drule bin'_wf_ConsD)
    by simp
next
  case (8 b1 b2 b3 t' t)
  then show ?case by fastforce
qed

lemma length_gn'_gt_0: "length (bin'_of_nat (gn' xs)) > 0"
  by (metis bin'_of_nat_start_True gn'_gt_0 length_greater_0_conv
      starts_with_True.simps(1))

lemma starts_with_True_gn'_eq_gn: "starts_with_True xs \<Longrightarrow>
                                   gn' xs = gn (bin_of_bin' xs)"
  unfolding gn'_def by (induction xs rule: bij_bin'_bin.induct) simp_all

lemma length_gn'_gt: "bin'_wf xs \<Longrightarrow> length (bin'_of_nat (gn' xs)) > length xs div 2"
  unfolding gn'_def using length_bij_bin'_bin_ge by force

lemma length_gn'_le: "bin'_wf xs \<Longrightarrow> length (bin'_of_nat (gn' xs)) \<le> Suc (length xs)"
  unfolding gn'_def apply simp
  by (metis add_leD1 even_two_times_div_two length_bij_bin'_bin_upper_bound
      nat_mult_le_cancel1 odd_two_times_div_two_succ pos2)

lemma eT_length_bij_bin_bin': "ends_in True xs \<Longrightarrow>
                               length (bij_bin_bin' xs) = Suc (length xs) div 2"
  by (induction xs rule: bij_bin_bin'.induct) simp_all

lemma ends_in_True_bij_bin'_bin_iff: "bin'_wf xs \<Longrightarrow>
                                      ends_in True (bij_bin'_bin xs) \<longleftrightarrow>
                                      starts_with_True xs"
proof (induction xs rule: bij_bin'_bin.induct)
  case 1
  then show ?case by simp
next
  case (2 t)
  then show ?case by simp
next
  case (3 t)
  then show ?case by fastforce
next
  case (4 b t)
  then show ?case by fastforce
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
  then show ?case by fastforce
qed

lemma starts_with_True_bij_bin_bin'_iff: "starts_with_True (bij_bin_bin' xs) \<longleftrightarrow>
                                          ends_in True xs"
proof (induction xs rule: bij_bin_bin'.induct)
  case (1 t)
  then show ?case by simp
next
  case (2 t)
  then show ?case by (simp add: starts_with_True_group_2)
next
  case 3
  then show ?case by simp
qed

lemma starts_with_TF_odd_length_gn': "bin'_wf xs \<Longrightarrow> starts_with [True, False] xs \<Longrightarrow>
                                      odd (length (bin_of_nat (gn' xs)))"
  unfolding gn'_def gn_def
proof (induction xs rule: bij_bin'_bin.induct)
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
  then show ?case by simp
next
  case (5 t)
  then show ?case apply simp
    apply (drule bin'_wf_ConsD)
    by simp
next
  case (6 t)
  then show ?case by simp
next
  case (7 t)
  then show ?case by simp
next
  case (8 b1 b2 b3 t' t)
  then show ?case by simp
qed

lemmas test = bij_bin'_bin.induct

lemma bij_bin'_bin_length_ge_induct [consumes 1]:
   "length x \<ge> n \<Longrightarrow> (\<And>xs. length xs = n \<Longrightarrow> P xs) \<Longrightarrow>
    (\<And>t. length t \<ge> n \<Longrightarrow> P t \<Longrightarrow> P ([False, False] # t)) \<Longrightarrow>
    (\<And>t. Suc (length t) \<ge> n \<Longrightarrow> P ([] # t)) \<Longrightarrow>
    (\<And>b t. Suc (length t) \<ge> n \<Longrightarrow> P ([b] # t)) \<Longrightarrow>
    (\<And>t. Suc (length t) \<ge> n \<Longrightarrow> P ([True, False] # t)) \<Longrightarrow>
    (\<And>t. Suc (length t) \<ge> n \<Longrightarrow> P ([False, True] # t)) \<Longrightarrow>
    (\<And>t. Suc (length t) \<ge> n \<Longrightarrow> P ([True, True] # t)) \<Longrightarrow>
    (\<And>b1 b2 b3 t' t. Suc (length t) \<ge> n \<Longrightarrow> P ((b1 # b2 # b3 # t') # t)) \<Longrightarrow> P x"
proof (induction x arbitrary: n rule: bij_bin'_bin.induct)
  case 1
  then show ?case by simp
next
  case (2 t)
  then show ?case using le_Suc_eq length_Cons by auto
next
  case (3 t)
  then show ?case by simp
next
  case (4 b t)
  then show ?case by simp
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
  then show ?case by simp
qed
                                  
lemma bij_bin'_bin_repl_FF: "bij_bin'_bin (replicate k [False, False]) = replicate k False"
  apply (induction k)
   apply auto
  by (simp add: replicate_append_same)

lemma bij_bin_bin'_repl_F: "bij_bin_bin' (replicate k False) = replicate k [False, False]"
  apply (induction k)
   apply auto
  by (metis bij_bin_bin'.simps(1) replicate_append_same)

lemma length_bij_bin_bin'_strict_mono: "Suc (bit_length n) < bit_length m \<Longrightarrow>
       length (bij_bin_bin' (bin_of_nat n)) < length (bij_bin_bin' (bin_of_nat m))"
proof (induction "bin_of_nat n" arbitrary: n m rule: bij_bin_bin'.induct)
  case (1 t)
  then show ?case
    by (metis bit_len_gt_0_iff gn_inv_of_bin length_greater_0_conv snoc_eq_iff_butlast)
next
  case IH: (2 t)
  then show ?case unfolding IH(1) [symmetric]
  proof simp
    assume a1: "Suc (Suc (length t)) < length (bin_of_nat m)"
    have "m \<noteq> 0" using a1 by (metis bin_of_nat.simps(1) less_nat_zero_code list.size(3))
    hence "ends_in True (bin_of_nat m)" by simp
    then obtain mp :: bin where mp_def: "bin_of_nat m = mp @ [True]" by (rule exE)
    show "Suc (length t div 2) < length (bij_bin_bin' (bin_of_nat m))"
      unfolding mp_def apply simp
      using a1 unfolding mp_def by simp
  qed
next
  case 3
  then show ?case apply simp
    by (metis bij_bin'_bin.simps(1) bij_bin'_bin_bin' less_nat_zero_code list.size(3))
qed

lemma length_bij_bin_bin'_mono: "bit_length n < bit_length m \<Longrightarrow>
       length (bij_bin_bin' (bin_of_nat n)) \<le> length (bij_bin_bin' (bin_of_nat m))"
proof (induction "bin_of_nat n" arbitrary: n m rule: bij_bin_bin'.induct)
  case (1 t)
  then show ?case
    by (metis bin_of_nat.simps(1) bin_of_nat_end_True nat_less_le snoc_eq_iff_butlast
        zero_le)
next
  case (2 t)
  then show ?case
    by (metis bij_bin'_bin_bin' bij_bin_bin'_wf bit_len_gt_0_iff dual_order.strict_iff_order
        gn'_defs(1) gn'_length_mono gn_inv_of_bin gn_length_mono leD leI
        length_greater_0_conv list.size(3) starts_with_True_bij_bin_bin'_iff)
next
  case 3
  then show ?case by simp
qed

lemma length_bij_bin_bin'_eq: "bit_length n = bit_length m \<Longrightarrow>
       length (bij_bin_bin' (bin_of_nat n)) = length (bij_bin_bin' (bin_of_nat m))"
proof (induction "bin_of_nat n" arbitrary: n m rule: bij_bin_bin'.induct)
  case (1 t)
  then show ?case
    by (metis append1_eq_conv bit_len_gt_0_iff gn_inv_of_bin length_greater_0_conv)
next
  case (2 t)
  then show ?case
    by (metis bit_len_gt_0_iff eT_length_bij_bin_bin' gn_inv_of_bin length_greater_0_conv)
next
  case 3
  then show ?case by simp
qed

lemma bij_bin_bin'_length_Cons_le: "length (bij_bin_bin' t) \<le> length (bij_bin_bin' (h#t))"
proof (induction t rule: bij_bin_bin'.induct)
  case (1 t)
  then show ?case
    by (metis Cons_eq_append_conv Suc_le_length_iff bij_bin_bin'.simps(1) length_Suc_conv)
next
  case (2 t)
  have 1: "h # t @ [True] = (h#t)@[True]" by simp
  show ?case unfolding 1 bij_bin_bin'.simps by simp
next
  case 3
  then show ?case by simp
qed

lemma length_bij_bin_bin'_rev_mono1:
  fixes w1 w2 :: bin
  assumes "msb_index w1 < msb_index w2"
      and "length w1 \<ge> length w2"
    shows "length (bij_bin_bin' w1) \<ge> length (bij_bin_bin' w2)"
proof (cases "True \<in> set w1")
  case w1_T: True
  then show ?thesis
  proof (cases "True \<in> set w2")
    case w2_T: True
    obtain p1 :: bin and k1 :: nat where w1_def: "w1 = p1 @ [True] @ replicate k1 False"
      using w1_T
      by (metis (full_types) append_Cons append_Nil replicate_length_same split_list_last)
    obtain p2 :: bin and k2 :: nat where w2_def: "w2 = p2 @ [True] @ replicate k2 False"
      using w2_T
      by (metis (full_types) append_Cons append_Nil replicate_length_same split_list_last)
    have 1: "k1 > k2" using assms(1, 2) unfolding w1_def w2_def msb_index_def
      apply (subst (asm) last_with_index_app1 [where i=0])
        apply auto
      apply (subst (asm) last_with_index_Cons2)
       apply auto
      apply (subst (asm) last_with_index_app1 [where i=0])
        apply auto
      apply (subst (asm) last_with_index_Cons2)
      by simp_all
    have 2: "k1 = length w1 - msb_index w1 - 1" unfolding w1_def msb_index_def
      apply (subst last_with_index_app1 [where i=0])
        apply auto
      apply (subst last_with_index_Cons2)
      by simp_all
    have 3: "k2 = length w2 - msb_index w2 - 1" unfolding w2_def msb_index_def
      apply (subst last_with_index_app1 [where i=0])
        apply auto
      apply (subst last_with_index_Cons2)
      by simp_all
    have 4: "length (bij_bin_bin' (xs @ [True] @ replicate n False)) =
             n + Suc (length xs div 2)"
      for xs :: bin and n :: nat
    proof (induction n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      have 1: "xs @ [True] @ False \<up> Suc n = (xs @ True # False \<up> n) @ [False]"
        by (simp add: replicate_append_same)
      show ?case unfolding 1 bij_bin_bin'.simps apply simp
        using Suc by simp
    qed
    have 5: "length p1 = length w1 - k1 - 1" unfolding w1_def by simp
    have 6: "length p2 = length w2 - k2 - 1" unfolding w2_def by simp
    have 7: "msb_index w1 < length w1" unfolding msb_index_def
      by (metis 1 2 diff_is_0_eq' last_with_index_upper_bound le_neq_implies_less
          less_or_eq_imp_le less_zeroE msb_index_def zero_less_one)
    have 8: "msb_index w2 < length w2" unfolding msb_index_def
      by (metis last_with_index_none last_with_index_within_bounds length_pos_if_in_set
          w2_T)
    show ?thesis unfolding w1_def w2_def using 4 [of p2 k2] 4 [of p1 k1]
      apply simp unfolding 2 3 5 6 using 7 8 apply simp
      using assms by linarith
  next
    case w2_F: False
    then obtain k :: nat where w2_def: "w2 = replicate k False"
      by (metis (full_types) replicate_length_same)
    have 1: "msb_index (replicate n False) = 0" for n :: nat
      unfolding msb_index_def by (subst last_with_index_none) simp_all
    have 2: "msb_index w1 = 0" using assms(1) 1 unfolding w2_def by simp
    have 3: "starts_with True w1" using 2 w1_T unfolding msb_index_def
      by (metis (full_types) eq_id_iff in_set_conv_nth last_with_index_has_property
          list.set_cases nth_Cons_0)
    then obtain s1 :: bin where w1_def: "w1 = True#s1" by auto
    have "msb_index w1 > 0" unfolding msb_index_def w1_def
          using 1 assms(1) w2_def by auto
    thus ?thesis using 2 by simp
  qed
next
  case False
  then obtain k :: nat where w1_def: "w1 = replicate k False"
    by (metis (full_types) replicate_length_same)
  have 1: "msb_index (replicate n False) = 0" for n :: nat
      unfolding msb_index_def by (subst last_with_index_none) simp_all
  show ?thesis using assms unfolding w1_def 1 bij_bin_bin'_repl_F apply simp
    by (metis bij_bin'_bin_bin' bij_bin_bin'_wf le_trans length_bij_bin'_bin_ge)
qed

lemma length_bij_bin_bin'_rev_mono2:
  fixes w1 w2 :: bin
  assumes "msb_index w1 = msb_index w2"
      and "msb_index w1 > 0"
      and "length w1 \<ge> length w2"
    shows "length (bij_bin_bin' w1) \<ge> length (bij_bin_bin' w2)"
proof -
  have 1: "True \<in> set w1" using assms(2) unfolding msb_index_def
    by (metis (full_types) id_def in_set_conv_nth last_with_index_none nless_le)
  have 2: "True \<in> set w2" using assms(2) unfolding assms(1) unfolding msb_index_def
    by (metis (full_types) id_apply in_set_conv_nth last_with_index_none
        order_less_imp_not_less)
  obtain p1 :: bin and k1 :: nat where w1_def: "w1 = p1 @ [True] @ replicate k1 False"
    using 1
    by (metis (full_types) append_Cons append_Nil replicate_length_same split_list_last)
  obtain p2 :: bin and k2 :: nat where w2_def: "w2 = p2 @ [True] @ replicate k2 False"
    using 2
    by (metis (full_types) append_Cons append_Nil replicate_length_same split_list_last)
  have 3: "length p1 = length p2"
    using assms(1, 2) unfolding w1_def w2_def msb_index_def apply simp
    apply (subst (asm) last_with_index_app1 [where i=0])
      apply auto
    apply (subst (asm) last_with_index_app1 [where i=0])
      apply auto
    apply (subst (asm) last_with_index_Cons2)
     apply auto
    apply (subst (asm) last_with_index_Cons2)
     apply auto
    apply (subst last_with_index_Cons2)
    by simp_all
  have 4: "k1 \<ge> k2"
    using assms(3) unfolding w1_def w2_def using 3 by simp
  have 5: "length (bij_bin_bin' (xs @ [True] @ replicate n False)) =
             n + Suc (length xs div 2)"
      for xs :: bin and n :: nat
    proof (induction n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      have 1: "xs @ [True] @ False \<up> Suc n = (xs @ True # False \<up> n) @ [False]"
        by (simp add: replicate_append_same)
      show ?case unfolding 1 bij_bin_bin'.simps apply simp
        using Suc by simp
    qed
  show "length (bij_bin_bin' w2) \<le> length (bij_bin_bin' w1)"
    unfolding w1_def w2_def using 3 4 5 [of p1 k1] 5 [of p2 k2] by simp
qed

lemma length_bij_bin_bin'_lower_bound: "length (bij_bin_bin' w) \<ge> length w div 2"
  by (metis Suc_1 bij_bin'_bin_bin' bij_bin_bin'_wf div_le_mono
      length_bij_bin'_bin_upper_bound nat.simps(3) nonzero_mult_div_cancel_left)

lemma length_bij_bin_bin'_upper_bound: "length (bij_bin_bin' w) \<le> length w"
  using length_bij_bin'_bin_ge by fastforce

lemma bij_bin'_bin_even_length: "bin'_wf t \<Longrightarrow> even (length (bij_bin'_bin ([True, b]#t)))"
proof (induction t rule: bij_bin'_bin.induct)
  case 1
  then show ?case apply simp
    by (metis gcd_nat.eq_iff group_2.simps(2) group_2_bin'_wf length_Cons
        length_bij_bin'_bin_starts_with_TrueX list.size(3) numeral_1_eq_Suc_0
        numeral_Bit0_eq_double)
next
  case (2 t)
  hence 1: "even (length (bij_bin'_bin ([True, b] # t)))" and 2: "bin'_wf t"
    by fastforce+
  have 3: "length (bij_bin'_bin ([True, b] # [False, False] # t)) =
           length (bij_bin'_bin ([True, b] # t)) + 2" apply simp
    by (smt (z3) 2 append_Cons append_self_conv2 bin'_wfE bin'_wfI bin'_wf_length
        flatten.simps(2) insert_iff length_Cons length_bij_bin'_bin_starts_with_TrueX
        list.set(2))
  then show ?case using 1 by simp
next
  case (3 t)
  then show ?case by fastforce
next
  case (4 b t)
  then show ?case by fastforce
next
  case (5 t)
  then show ?case
    using bin'_wfI length_bij_bin'_bin_starts_with_TrueX by fastforce
next
  case (6 t)
  then show ?case using bin'_wfI length_bij_bin'_bin_starts_with_TrueX by fastforce
next
  case (7 t)
  then show ?case using bin'_wfI length_bij_bin'_bin_starts_with_TrueX by fastforce
next
  case (8 b1 b2 b3 t' t)
  then show ?case by fastforce
qed
end