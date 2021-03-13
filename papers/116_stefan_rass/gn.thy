theory gn
  imports Main HOL.HOL HOL.Num
begin

(* actually we could just use num instead of "bool list" since both
   types are constructed exactly the same way as shown below *)
fun num_of_word :: "bool list \<Rightarrow> num" where
"num_of_word Nil = num.One" |
"num_of_word (True#t) = num.Bit1 (num_of_word t)" |
"num_of_word (False#t) = num.Bit0 (num_of_word t)"

fun word_of_num :: "num \<Rightarrow> bool list" where
"word_of_num num.One = Nil" |
"word_of_num (num.Bit1 t) = True#(word_of_num t)" |
"word_of_num (num.Bit0 t) = False#(word_of_num t)"

lemma word_num_id [simp]: "word_of_num (num_of_word x) = x"
  apply (induction x)
  apply (simp)
  apply (metis num_of_word.simps num_of_word.simps word_of_num.simps(2) word_of_num.simps(3))
  done

fun gn :: "bool list \<Rightarrow> nat" where
  "gn w = nat_of_num (num_of_word w)"

theorem gn_inj: "gn x = gn y \<Longrightarrow> x = y"
proof -
  assume "gn x = gn y"
  hence "num_of_word x = num_of_word y" using num_eq_iff by auto
  then have "word_of_num (num_of_word x) = word_of_num (num_of_word y)" by simp
  from this show ?thesis by simp
qed

theorem gn_gt_0[simp]: "gn w > 0"
  by (simp add: nat_of_num_pos)

(* is a number a gödel number *)
fun is_gn :: "nat \<Rightarrow> bool"
  where "is_gn n = (n > 0)"

(* inverse: retrieve word from gödel number, assuming it is a valid gn (is_gn n = True) *)
fun gn_inv :: "nat \<Rightarrow> bool list"
  where "gn_inv n = word_of_num (num_of_nat n)"

lemma "is_gn n \<Longrightarrow> gn (gn_inv n) = n"
  oops

theorem "is_gn n \<Longrightarrow> \<exists>w. gn w = n"
  oops