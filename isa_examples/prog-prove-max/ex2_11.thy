theory ex2_11
  imports Main
begin

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "[exp, int] \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const a) x = a" |
"eval (Add a b) x = eval a x + eval b x" |
"eval (Mult a b) x = eval a x * eval b x"

fun evalp :: "[int list, int] \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (a # p) x = a + x * evalp p x"

fun addp :: "[int list, int list] \<Rightarrow> int list" where
"addp [] p = p" |
"addp p [] = p" |
"addp (a # p) (b # q) = (a+b) # (addp p q)"

lemma addp1: "evalp (addp a b) x = evalp a x + evalp b x"
  by (induction a b rule: addp.induct) (auto simp add: algebra_simps)

fun multp :: "[int list, int list] \<Rightarrow> int list" where
"multp [] p = []" |
"multp q [] = []" |
"multp [a] (b#p) = (a*b) # multp [a] p" |
"multp (a#p) q = addp (multp [a] q) (0#(multp p q))"

lemma multp1: "evalp (multp a b) x = evalp a x * evalp b x"
  by (induction a b rule: multp.induct) (auto simp add: addp1 algebra_simps)

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs (Const a) = [a]" |
"coeffs Var = [0,1]" |
"coeffs (Add a b) = addp (coeffs a) (coeffs b)" |
"coeffs (Mult a b) = multp (coeffs a) (coeffs b)"

lemma "evalp (coeffs e) x = eval e x"
  by (induction e) (auto simp add: addp1 multp1 algebra_simps)

end