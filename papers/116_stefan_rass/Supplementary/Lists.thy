theory Lists
  imports Main
begin

\<comment> \<open>From \<^session>\<open>Universal_Turing_Machine\<close>.\<close>
abbreviation replicate_exponent :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" ("_ \<up> _" [100, 99] 100)
  where "x \<up> n \<equiv> replicate n x"

lemma set_replicate_subset: "set (x \<up> n) \<subseteq> {x}" by auto

lemma map2_replicate: "map2 f (x \<up> n) ys = map (f x) (take n ys)"
  unfolding zip_replicate1 map_map by simp

lemma map2_singleton:
  assumes "set xs \<subseteq> {x}" and "length xs = length ys"
  shows "map2 f xs ys = map (f x) ys"
  using assms map2_replicate replicate_eqI
  by (metis empty_iff map_snd_zip map_snd_zip_take min.idem singletonD subset_singletonD)

lemma map2_id:
  assumes "length xs = length ys"
      and "set xs \<subseteq> {x}"
      and "f x = id"
    shows "map2 f xs ys = ys"
  apply (subst map2_singleton)
  using assms(1-2) apply blast+
  unfolding assms(3) list.map_id0 id_apply ..

lemma nth_map2:
  assumes "i < length xs" and "i < length ys"
  shows "map2 f xs ys ! i = f (xs ! i) (ys ! i)"
  using assms by (subst nth_map) auto

lemma len_tl_Cons: "xs \<noteq> [] \<Longrightarrow> length (x # tl xs) = length xs"
  by simp

lemma drop_diff_length: "n \<le> length xs \<Longrightarrow> length (drop (length xs - n) xs) = n"
  by simp

lemma drop_eq_le:
  assumes "L \<ge> l"
    and "drop l xs = drop l ys"
  shows "drop L xs = drop L ys"
proof -
  from \<open>L \<ge> l\<close> obtain n where "L = n + l"
    unfolding add.commute[of _ l] by (rule less_eqE)
  have "drop L xs = drop n (drop l xs)"
    unfolding \<open>L = n + l\<close> by (rule drop_drop[symmetric])
  also have "... = drop n (drop l ys)"
    unfolding \<open>drop l xs = drop l ys\<close> ..
  also have "... = drop L ys"
    unfolding \<open>L = n + l\<close> by (rule drop_drop)
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

abbreviation "pad n x xs \<equiv> xs @ x \<up> (n - length xs)"

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

declare list_all_iff[iff]
lemma list_all_set_map[iff]: "set (map f xs) \<subseteq> A \<longleftrightarrow> list_all (\<lambda>x. f x \<in> A) xs" by auto

lemma map_inv_into_map_id:
  fixes f::"'a \<Rightarrow> 'b"
  assumes "inj_on f A"
      and "set as \<subseteq> A"
    shows "map (inv_into A f) (map f as) = as"
  using assms inv_into_f_f
  by (metis (no_types, lifting) list.map_comp map_idI o_apply subset_iff)

lemma map_map_inv_into_id:
  fixes f::"'a \<Rightarrow> 'b"
  assumes "inj_on f A"
      and "set bs \<subseteq> f ` A"
    shows "map f (map (inv_into A f) bs) = bs"
  using assms f_inv_into_f
  by (metis (no_types, lifting) list.map_comp map_idI o_apply subset_iff)

lemma nths_insert_interval_less:
  assumes "length w \<ge> 1"
    and "k1 \<ge> 1"
  shows "nths w ({0} \<union> {k1..<k}) = hd w # nths w {k1..<k}" using assms
proof (induction w)
  case (Cons a w)
  from \<open>k1 \<ge> 1\<close> show ?case unfolding nths_Cons by force
qed (* case "w = []" by *) simp

lemma length_nths_interval: "length (nths xs {n..<m}) = min (length xs) m - n"
proof -
  have "length (nths xs {n..<m}) = card {i. n \<le> i \<and> i < length xs \<and> i < m}"
    unfolding length_nths atLeastLessThan_iff by meson
  also have "... = card {n..<min (length xs) m}"
    unfolding min_less_iff_conj[symmetric] by (intro arg_cong[where f=card] set_eqI) simp
  also have "... = min (length xs) m - n" by (fact card_atLeastLessThan)
  finally show ?thesis .
qed

end
