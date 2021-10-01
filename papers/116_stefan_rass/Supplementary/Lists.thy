theory Lists
  imports Main
begin

lemma len_tl_Cons: "xs \<noteq> [] \<Longrightarrow> length (x # tl xs) = length xs" by simp

lemma drop_eq_le:
  assumes "L \<ge> l"
    and "drop l xs = drop l ys"
  shows "drop L xs = drop L ys"
proof -
  from \<open>L \<ge> l\<close> obtain n where "L = n + l" unfolding add.commute[of _ l] by (rule less_eqE)
  have "drop L xs = drop n (drop l xs)" unfolding \<open>L = n + l\<close> by (rule drop_drop[symmetric])
  also have "... = drop n (drop l ys)" unfolding \<open>drop l xs = drop l ys\<close> ..
  also have "... = drop L ys" unfolding \<open>L = n + l\<close> by (rule drop_drop)
  finally show "drop L xs = drop L ys" .
qed

lemma inj_append:
  fixes xs ys :: "'a list"
  shows inj_append_L: "inj (\<lambda>xs. xs @ ys)"
    and inj_append_R: "inj (\<lambda>ys. xs @ ys)"
  using append_same_eq by (intro injI, simp)+

lemma infinite_lists:
  assumes "\<forall>l. \<exists>xs\<in>X. length xs \<ge> l"
  shows "infinite X"
proof -
  from assms have "\<nexists>n. \<forall>s\<in>X. length s < n" by (fold not_less) simp
  then show "infinite X" using finite_maxlen by (rule contrapos_nn)
qed

abbreviation "pad n x xs \<equiv> xs @ replicate (n - length xs) x"

lemma pad_length: "length (pad n x xs) = max n (length xs)"
  by simp

lemma pad_le_length[simp]: "length xs \<le> n \<Longrightarrow> length (pad n x xs) = n"
  by simp

subsection\<open>\<open>ends_in\<close> - An Alternative to \<^const>\<open>last\<close>\<close>

abbreviation (input) ends_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ends_in x xs \<equiv> (\<exists>ys. xs = ys @ [x])"

lemma ends_inI[intro]: "ends_in x (xs @ [x])" by blast

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
