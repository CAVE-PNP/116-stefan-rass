theory gn
  imports Main HOL.Num nat_bin
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
type_synonym lang = "word set"

(* gödel number *)
definition gn :: "word \<Rightarrow> nat" where "gn \<equiv> nat_of_num"

(* is a number a gödel number *)
definition is_gn :: "nat \<Rightarrow> bool" where "is_gn n = (n > 0)"

(* inverse of the gödel number *)
definition gn_inv :: "nat \<Rightarrow> word" where "gn_inv \<equiv> num_of_nat"

declare gn_def[simp] is_gn_def[simp] gn_inv_def[simp]

lemma gn_inj: "inj gn"
  unfolding gn_def using num_eq_iff injI[of nat_of_num] by blast

(* correctness of the inverse *)
corollary inv_gn_id [simp]: "is_gn n \<Longrightarrow> gn (gn_inv n) = n" using num_of_nat_inverse by simp
corollary gn_inv_id [simp]: "gn_inv (gn (x)) = x" using nat_of_num_inverse by simp

corollary ex_gn: "is_gn n \<Longrightarrow> \<exists>w. gn w = n"
  using inv_gn_id by blast

(* more properties *)
lemma gn_inv_inj: "inj_on gn_inv {0<..}"
proof (intro inj_on_inverseI)
  fix x::nat assume "x \<in> {0<..}"
  then have "is_gn x" unfolding is_gn_def greaterThan_iff .
  with inv_gn_id show "gn (gn_inv x) = x" .
qed

lemma gn_gt_0: "gn w > 0"
  by (induction w) auto


(* gn of nat for convenience, as defined in ch 4.1 *)
definition gn' :: "nat \<Rightarrow> nat" where "gn' n = n"

declare gn'_def[simp]

lemma gn'D: "n > 0 \<Longrightarrow> gn' n = gn (num_of_nat n)"
  using inv_gn_id by simp


subsection\<open>bit-strings\<close>

(* conversion to bit strings *)
fun word_of_bin :: "bin \<Rightarrow> word" where
  "word_of_bin Nil = num.One" |
  "word_of_bin (True # t) = num.Bit1 (word_of_bin t)" |
  "word_of_bin (False # t) = num.Bit0 (word_of_bin t)"

fun bin_of_word :: "word \<Rightarrow> bin" where
  "bin_of_word num.One = Nil" |
  "bin_of_word (num.Bit1 t) = True # (bin_of_word t)" |
  "bin_of_word (num.Bit0 t) = False # (bin_of_word t)"

fun app :: "word \<Rightarrow> word \<Rightarrow> word" (infixr "@@" 65) where
  "app v w = word_of_bin (bin_of_word v @ bin_of_word w)"

fun drp :: "nat \<Rightarrow> word \<Rightarrow> word" where
  "drp n w = word_of_bin (drop n (bin_of_word w))"

(* correctness and relations *)
lemma bin_word_bin_id [simp]: "bin_of_word (word_of_bin x) = x"
proof (induction x)
  case (Cons a x) thus ?case by (cases a) simp_all
qed (* case "x = []" by *) simp

lemma word_bin_word_id [simp]: "word_of_bin (bin_of_word x) = x"
  by (induction x) auto

corollary word_bin_inv:
  shows word_of_bin_inv: "inv word_of_bin = bin_of_word"
    and bin_of_word_inv: "inv bin_of_word = word_of_bin"
  by (simp_all add: inv_equality)

corollary word_bin_bij:
  shows word_of_bin_bij: "bij word_of_bin"
    and bin_of_word_bij: "bij bin_of_word"
proof -
  show "bij word_of_bin" by (intro bijI', metis bin_word_bin_id, metis word_bin_word_id)
  with bij_imp_bij_inv[of word_of_bin] show "bij bin_of_word" unfolding word_of_bin_inv .
qed

(* relation to bin *)
lemma gn_bin_eq: "gn w = nat_of_bin ((bin_of_word w) @ [True])"
  by (induction w) auto


subsection\<open>bit-length\<close>

fun len :: "word \<Rightarrow> nat" where
  "len num.One = 0" |
  "len (num.Bit0 w) = Suc (len w)" |
  "len (num.Bit1 w) = Suc (len w)"

definition bit_length :: "nat \<Rightarrow> nat" where
  "bit_length n \<equiv> len (num_of_nat n) + 1"

declare bit_length_def[simp]

corollary len_gt_0: "w \<noteq> num.One \<Longrightarrow> len w > 0" by (cases w) simp_all

corollary len_eq_0_iff: "w = num.One \<longleftrightarrow> len w = 0" by (cases w) simp_all

corollary len_Cons_eq: "len (num.Bit0 w) = len (num.Bit1 w)" by simp

lemma num_of_nat_double': "0 < n \<Longrightarrow> num_of_nat (n + n + 1) = num.Bit1 (num_of_nat n)"
  by (induction n) auto

lemma bit_len_even_odd: "bit_length (2 * n) = bit_length (2 * n + 1)"
proof (cases "n > 0")
  case False thus ?thesis by simp
next
  case True
  have "bit_length (2 * n) = len (num_of_nat (n + n)) + 1" unfolding mult_2 by simp
  also have "... = len (num.Bit0 (num_of_nat n)) + 1" using num_of_nat_double and \<open>n > 0\<close> by simp
  also have "... = len (num.Bit1 (num_of_nat n)) + 1" unfolding len_Cons_eq ..
  also have "... = len (num_of_nat (n + n + 1)) + 1" using num_of_nat_double' and \<open>n > 0\<close> by simp
  also have "... = bit_length (2 * n + 1)" unfolding mult_2 by simp
  finally show ?thesis .
qed

lemma word_len_eq_bin_len:
  "len w = length (bin_of_word w)"
  by (induction w) auto

lemma word_len_eq_bin_len':
  "len (word_of_bin b) = length b"
  using word_len_eq_bin_len by simp

lemmas word_bin_iso = word_len_eq_bin_len word_len_eq_bin_len' bin_word_bin_id word_bin_word_id

lemma drp_len[simp]:
  "len (drp n w) = len w - n"
  unfolding drp.simps
  using word_bin_iso by simp

lemma drp_prefix[simp]:
  "drp (len p) (p @@ w) = w"
  unfolding drp.simps
  using word_bin_iso by force

lemma app_len[simp]: "len (w @@ v) = len w + len v"
  unfolding app.simps
  using word_bin_iso by force

lemma num_of_nat_double:
  assumes "n > 0"
  shows "num_of_nat (2 * n) = num.Bit0 (num_of_nat n)"
  using assms num_of_nat_inverse num_eq_iff by simp

corollary bit_len_double:
  assumes "n > 0"
  shows "bit_length (2 * n) = 1 + bit_length n"
  using assms num_of_nat_double by simp


lemma nat_of_num_max: "nat_of_num n < 2 ^ (len n + 1)" by (induction n) auto
lemma nat_of_num_min: "nat_of_num n \<ge> 2 ^ (len n)" by (induction n) auto

lemma num_of_nat_lengths: "len n < len m \<Longrightarrow> nat_of_num n < nat_of_num m"
proof -
  assume "len n < len m"
  then have l: "len n + 1 \<le> len m" by simp

  have "nat_of_num n < 2 ^ (len n + 1)" using nat_of_num_max .
  also have "... \<le> 2 ^ (len m)" using l by (subst power_increasing_iff) auto
  also have "... \<le> nat_of_num m" using nat_of_num_min by simp
  finally show ?thesis .
qed

end
