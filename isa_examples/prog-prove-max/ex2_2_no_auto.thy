theory ex2_2_no_auto
  imports Main HOL.HOL
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  add_0_n : "add 0 n = n" |
  add_Sm_n : "add (Suc m) n = Suc(add m n)"


find_theorems "add 0 ?n = ?n"
thm add.simps(1)[of "0"]

lemma add_m_0 [simp]: 
  fixes m::nat
  shows "add m 0 = m"
proof (induction m)
  case 0
  show ?case by (rule add_0_n) (* or "add.simps(1)". "add.simps" also works *)
      (* more exact: by (rule add_0_n[of 0]) *)
next
  case (Suc m)
    (* assume "add m 0 = m" *)
  hence "Suc (add m 0) = Suc m" .. (* by (rule arg_cong) *)
  thus ?case by (subst add_Sm_n) (* or "add.simps(2)" *)
      (* thus "add (Suc m) 0 = Suc m" by (subst add_Sm_n[of m 0]) *)
qed

lemma add_m_Sn [simp] : 
  fixes m n
  shows "add m (Suc n) = Suc(add m n)"
proof (induction m)
  case 0
  have "add 0 (Suc n) = Suc n" by (rule add_0_n) (* [of "Suc n"] *)
  thus ?case by (subst add_0_n) (* [of n] *)
next
  case (Suc m)
    (* assume "add m (Suc n) = Suc (add m n)" *)
  hence "Suc (add m (Suc n)) = Suc (Suc (add m n))" .. (* by (rule arg_cong) *)
  hence "add (Suc m) (Suc n) = Suc (Suc (add m n))" by (subst add_Sm_n)
  thus "add (Suc m) (Suc n) = Suc (add (Suc m) n)" by (subst add_Sm_n)
qed

lemma add_assoc: 
  fixes a b c
  shows "add (add a b) c = add a (add b c)"
proof (induction a)
  case 0
  have "add b c = add b c" ..
  hence "add (add 0 b) c = add b c" by (subst add_0_n)
  thus ?case by (subst add_0_n)
next
  case (Suc a)
    (* assume "add (add a b) c = add a (add b c)" *)
  hence "Suc (add (add a b) c) = Suc (add a (add b c))" ..
  hence "add (Suc (add a b)) c = Suc (add a (add b c))" by (subst add_Sm_n)
  hence "add (add (Suc a) b) c = Suc (add a (add b c))" by (subst add_Sm_n)
  thus "add (add (Suc a) b) c = add (Suc a) (add b c)" by (subst add_Sm_n)
qed


lemma add_comm: 
  fixes a b
  shows "add a b = add b a"
proof (induction a)
  case 0
  have "add 0 b = b" by (rule add_0_n)
  thus "add 0 b = add b 0" by (subst add_m_0)
next
  case (Suc a)
    (* assume "add a b = add b a" *)
  hence "Suc (add a b) = Suc (add b a)" ..
  hence "add (Suc a) b = Suc (add b a)" by (subst add_Sm_n)
  thus "add (Suc a) b = add b (Suc a)" by (subst add_m_Sn)
qed

end