theory ex3_1
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"


(* list items in a tree *)
fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node lchild item rchild) = contents lchild @ [item] @ contents rchild"

(* return set of items in a tree *)
fun set:: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}" |
  "set (Node l a r) = set l \<union> {a} \<union> set r"

(* check if tree is ordered AND values are between an upper and a lower bound *)
fun ord_between :: "[int tree, int, int] \<Rightarrow> bool" where
  "ord_between Tip _ _ = True" |
  "ord_between (Node l a r) lo hi = (ord_between l lo a \<and> lo \<le> a \<and> a \<le> hi \<and> ord_between r a hi)"

(* check if tree is ordered AND values are less than or equal an upper bound *)
fun ord_le :: "[int tree, int] \<Rightarrow> bool" where
  "ord_le Tip _ = True" |
  "ord_le (Node l a r) hi = (ord_le l a \<and> a \<le> hi \<and> ord_between r a hi)"

(* check if tree is ordered AND values are greater than or equal a lower bound *)
fun ord_ge :: "[int tree, int] \<Rightarrow> bool" where
  "ord_ge Tip _ = True" |
  "ord_ge (Node l a r) lo = (ord_between l lo a \<and> a \<ge> lo \<and> ord_ge r a)"

(* check if tree is ordered *)
fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True" |
  "ord (Node l a r) = (ord_le l a \<and> ord_ge r a)"

(* insert a value into an ordered tree keeping the order intact *)
fun ins :: "[int, int tree] \<Rightarrow> int tree" where 
  "ins a Tip = Node Tip a Tip" |
  "ins b (Node l a r) = (if a = b then Node l a r else (if a > b then (Node (ins b l) a r) else (Node l a (ins b r))))"

value "ins 2 (Node Tip (1) Tip)"


theorem "set (ins x t) = {x} \<union> set t"
  by (induction t rule: set.induct) auto

lemma l1: "((lo \<le> i) \<and> (i \<le> hi) \<and> (ord_between t lo hi)) \<longrightarrow> (ord_between (ins i t) lo hi)"
  by (induction t arbitrary: hi lo) auto

lemma l2: "(a \<ge> i \<and> ord_le t a) \<longrightarrow> ord_le (ins i t) a"
  by (induction t arbitrary: a) (auto simp add: l1)

lemma l3: "(a \<le> i \<and> ord_ge t a) \<longrightarrow> ord_ge (ins i t) a"
  by (induction t arbitrary: a) (auto simp add: l1)

theorem ord_ins_invariant: "ord t \<longrightarrow> ord (ins i t)"
  by (induction t) (auto simp add: l1 l2 l3)

end