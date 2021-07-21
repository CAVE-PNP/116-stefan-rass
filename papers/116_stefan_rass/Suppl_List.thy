theory Suppl_List
  imports Main
begin

lemma len_tl_Cons: "xs \<noteq> [] \<Longrightarrow> length (x # tl xs) = length xs" by simp


subsection\<open>An Alternative to \<^const>\<open>last\<close>\<close>

abbreviation (input) ends_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ends_in x xs \<equiv> (\<exists>ys. xs = ys @ [x])"


lemma ends_in_Cons: "ends_in y (x # xs) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> ends_in y xs"
  by (simp add: Cons_eq_append_conv)

lemma ends_in_last: "xs \<noteq> [] \<Longrightarrow> ends_in x xs \<longleftrightarrow> last xs = x"
proof (intro iffI)
  assume "xs \<noteq> []" and "last xs = x"
  from \<open>xs \<noteq> []\<close> have "butlast xs @ [last xs] = xs"
    unfolding snoc_eq_iff_butlast by (intro conjI) auto
  then show "ends_in x xs" unfolding \<open>last xs = x\<close> by (intro exI) (rule sym)
qed (* direction "\<longrightarrow>" by *) force

lemma ends_in_append: "ends_in x (xs @ ys) \<longleftrightarrow> (if ys = [] then ends_in x xs else ends_in x ys)"
proof (cases "ys = []")
  case False
  then have "xs @ ys \<noteq> []" by blast
  with ends_in_last have "ends_in x (xs @ ys) \<longleftrightarrow> last (xs @ ys) = x" .
  also have "... \<longleftrightarrow> last ys = x" unfolding \<open>ys \<noteq> []\<close>[THEN last_appendR] ..
  also have "... \<longleftrightarrow> ends_in x ys" using ends_in_last[symmetric] \<open>ys \<noteq> []\<close> .
  also have "... \<longleftrightarrow> (if ys = [] then ends_in x xs else ends_in x ys)" using \<open>ys \<noteq> []\<close> by simp
  finally show ?thesis .
qed (* case "ys = []" by *) simp

lemma ends_in_drop:
  assumes "k < length xs"
    and "ends_in x xs"
  shows "ends_in x (drop k xs)"
  using assms by force

end
