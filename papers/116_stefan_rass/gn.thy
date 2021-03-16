theory gn
  imports Main HOL.Num nat_bin
begin

type_synonym word = "bool list"

(* actually we could just use num instead of "bool list" since both
   types are constructed exactly the same way as shown below *)
fun num_of_word :: "word \<Rightarrow> num" where
  "num_of_word Nil = num.One" |
  "num_of_word (True#t) = num.Bit1 (num_of_word t)" |
  "num_of_word (False#t) = num.Bit0 (num_of_word t)"

fun word_of_num :: "num \<Rightarrow> word" where
  "word_of_num num.One = Nil" |
  "word_of_num (num.Bit1 t) = True#(word_of_num t)" |
  "word_of_num (num.Bit0 t) = False#(word_of_num t)"

lemma num_word_num_id [simp]: "word_of_num (num_of_word x) = x"
  apply (induction x)
   apply (simp)
  apply (metis (full_types) num_of_word.simps(2-3) word_of_num.simps(2-3))
  done

lemma word_num_word_id [simp]: "num_of_word (word_of_num x) = x"
  by (induction x) auto

(* definition of gödel number from ch 3.1, eqn (2) *)
fun gn :: "word \<Rightarrow> nat" where
  "gn w = nat_of_num (num_of_word w)"

theorem gn_inj: "gn x = gn y \<Longrightarrow> x = y"
proof -
  assume "gn x = gn y"
  hence "num_of_word x = num_of_word y" using num_eq_iff by simp
  then have "word_of_num (num_of_word x) = word_of_num (num_of_word y)" by simp
  from this show ?thesis by simp
qed

corollary gn_inj2: "inj gn"
  using gn_inj by (rule injI)

lemma gn_gt_0[simp]: "gn w > 0"
  by (simp add: nat_of_num_pos)

(* is a number a gödel number *)
fun is_gn :: "nat \<Rightarrow> bool"
  where "is_gn n = (n > 0)"

(* inverse: retrieve word from gödel number, assuming it is a valid gn (is_gn n = True) *)
fun gn_inv :: "nat \<Rightarrow> word"
  where "gn_inv n = word_of_num (num_of_nat n)"

(* correctness of the inverse *)
theorem inv_gn_id [simp]: "is_gn n \<Longrightarrow> gn (gn_inv n) = n"
  by (induction n) (simp_all add: nat_of_num_inc)

corollary ex_gn: "is_gn n \<Longrightarrow> \<exists>w. gn w = n"
  using inv_gn_id by blast

theorem gn_inv_id [simp]: "gn_inv (gn (x)) = x"
  by (simp add: nat_of_num_inverse)

(* relation to bin *)
lemma gn_bin_eq: "gn w = nat_of_bin (w @ [True])"
  by (induction w) auto

(* gn of nat for convenience, as defined in ch 4.1 *)
fun gn' :: "nat \<Rightarrow> nat" where
  "gn' n = gn (bin_of_nat n)"

(* TODO (?) gödel numbering of turing machines *)

end