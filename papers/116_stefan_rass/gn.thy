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

type_synonym bit_string = "bool list"

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
  by (metis greaterThan_iff inj_on_inverseI inv_gn_id is_gn_def)

lemma gn_gt_0: "gn w > 0"
  by (induction w) auto


(* conversion to bit strings *)
fun word_of_bin :: "bit_string \<Rightarrow> word" where
  "word_of_bin Nil = num.One" |
  "word_of_bin (True # t) = num.Bit1 (word_of_bin t)" |
  "word_of_bin (False # t) = num.Bit0 (word_of_bin t)"

fun bin_of_word :: "word \<Rightarrow> bit_string" where
  "bin_of_word num.One = Nil" |
  "bin_of_word (num.Bit1 t) = True # (bin_of_word t)" |
  "bin_of_word (num.Bit0 t) = False # (bin_of_word t)"

(* correctness and relations *)
lemma bin_word_bin_id [simp]: "bin_of_word (word_of_bin x) = x"
  by (induction x, simp, metis (full_types) word_of_bin.simps(2-3) bin_of_word.simps(2-3))

lemma word_bin_word_id [simp]: "word_of_bin (bin_of_word x) = x"
  by (induction x) auto

corollary word_bin_inv:
  shows word_of_bin_inv: "inv word_of_bin = bin_of_word"
    and bin_of_word_inv: "inv bin_of_word = word_of_bin"
  by (simp_all add: inv_equality)

corollary word_bin_bij:
  shows word_of_bin_bij: "bij word_of_bin"
    and bin_of_word_bij: "bij bin_of_word"
  by (metis bijI' bin_word_bin_id word_bin_word_id)+


(* relation to bin *)
lemma gn_bin_eq: "gn w = nat_of_bin ((bin_of_word w) @ [True])"
  by (induction w) auto

(* gn of nat for convenience, as defined in ch 4.1 *)
definition gn' :: "nat \<Rightarrow> nat" where
  "gn' n = n"

declare gn'_def[simp]

lemma gn'D: "n > 0 \<Longrightarrow> gn' n = gn (num_of_nat n)"
  using inv_gn_id by auto

end
