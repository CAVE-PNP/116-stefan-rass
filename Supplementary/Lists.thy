section\<open>Lists\<close>

theory Lists
  imports Main Misc "HOL-Library.Sublist"
begin

text\<open>Extends \<^theory>\<open>HOL.List\<close>.\<close>

lemma takeWhile_True[simp]: "takeWhile (\<lambda>x. True) = (\<lambda>x. x)" by fastforce


notation lists ("(_*)" [1000] 999) \<comment> \<open>Priorities taken from \<^const>\<open>rtrancl\<close>,
  to force parentheses on terms like \<^term>\<open>x \<in> (f A)*\<close>.
  Introducing an abbreviation would be nicer, since Ctrl+Click then shows the abbreviation,
  instead of directly jumping to \<^const>\<open>lists\<close>,
  but the abbreviation completely replaces references to \<^const>\<open>lists\<close>, which is confusing.\<close>
(*(* abbreviation kleene_star ("(_*)" [1000] 999) where "\<Sigma>* \<equiv> lists \<Sigma>" *)

lemma lists_member[iff]: "w \<in> \<Sigma>* \<longleftrightarrow> set w \<subseteq> \<Sigma>" by blast


\<comment> \<open>From \<^session>\<open>Universal_Turing_Machine\<close>.\<close>
abbreviation replicate_exponent :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" ("_ \<up> _" [100, 99] 100)
  where "x \<up> n \<equiv> replicate n x"

lemma set_replicate_subset: "set (x \<up> n) \<subseteq> {x}"
  unfolding set_replicate_conv_if by simp

lemma map2_replicate: "map2 f (x \<up> n) ys = map (f x) (take n ys)"
  unfolding zip_replicate1 map_map by simp

lemma replicate_set_eq: "set xs \<subseteq> {x} \<longleftrightarrow> xs = x \<up> length xs"
proof (intro iffI)
  assume "xs = x \<up> length xs"
  have "set (x \<up> length xs) \<subseteq> {x}" by (fact set_replicate_subset)
  then show "set xs \<subseteq> {x}" using \<open>xs = x \<up> length xs\<close> by simp
next
  assume "set xs \<subseteq> {x}"
  then show "xs = x \<up> length xs" by (blast intro: replicate_eqI)
qed

lemma replicate_eq: "xs = x \<up> length xs \<longleftrightarrow> (\<exists>n. xs = x \<up> n)"
proof (intro iffI)
  assume "\<exists>n. xs = x \<up> n"
  then obtain n where "xs = x \<up> n" ..
  then have "n = length xs" by simp
  with \<open>xs = x \<up> n\<close> show "xs = x \<up> length xs" by simp
qed (fact exI)

lemma map2_singleton:
  assumes "set xs \<subseteq> {x}"
    and ls: "length xs = length ys"
  shows "map2 f xs ys = map (f x) ys"
proof -
  from \<open>set xs \<subseteq> {x}\<close> have xs: "x \<up> length xs = xs" unfolding replicate_set_eq ..
  have "map2 f xs ys = map2 f (x \<up> length xs) ys" unfolding xs ..
  also have "... = map (f x) ys" unfolding map2_replicate ls by simp
  finally show ?thesis .
qed

lemma map2_id:
  assumes "length xs = length ys"
      and "set xs \<subseteq> {x}"
      and "f x = id"
    shows "map2 f xs ys = ys"
  using assms by (subst map2_singleton) auto

lemma nth_map2:
  assumes "i < length xs" and "i < length ys"
  shows "map2 f xs ys ! i = f (xs ! i) (ys ! i)"
  using assms by (subst nth_map) auto

lemma map2_same: "map2 f xs xs = map (\<lambda>x. f x x) xs" unfolding zip_same_conv_map by simp

lemma map2_eqI:
  assumes "zip xs' ys' = zip xs ys"
  shows "map2 f xs' ys' = map2 f xs ys"
  using assms by (rule arg_cong)

lemma take_eq[simp]: "take (length xs) xs = xs" by simp

lemma zip_eqI:
  fixes xs xs' :: "'a list" and ys ys' :: "'b list"
  defines l:  "l \<equiv> min (length xs) (length ys)"
  assumes l': "l = min (length xs') (length ys')"
    and lx: "take l xs' = take l xs"
    and ly: "take l ys' = take l ys"
  shows "zip xs' ys' = zip xs ys"
proof -
  have "zip xs' ys' = take l (zip xs' ys')" unfolding l' by simp
  also have "... = take l (zip xs ys)" unfolding take_zip lx ly ..
  also have "... = zip xs ys" unfolding l by simp
  finally show ?thesis .
qed


lemma map2_cong:
  assumes "\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x y = g x y"
  shows "map2 f xs ys = map2 g xs ys"
proof (rule list.map_cong0)
  fix xy
  assume "xy \<in> set (zip xs ys)"
  thus "(case xy of (x, y) \<Rightarrow> f x y) = (case xy of (x, y) \<Rightarrow> g x y)"
  proof (induction xy)
    case (Pair x y)
    with assms show ?case by fast
  qed
qed

lemma map2_cong':
  assumes "\<And>n. n < min (length xs) (length ys) \<Longrightarrow> f (xs ! n) (ys ! n) = g (xs ! n) (ys ! n)"
  shows "map2 f xs ys = map2 g xs ys"
proof (rule map2_cong)
  fix x y
  assume "(x, y) \<in> set (zip xs ys)"
  then obtain n where "zip xs ys ! n = (x, y)" and n_len: "n < min (length xs) (length ys)"
    unfolding in_set_conv_nth length_zip by blast
  then have x: "x = xs ! n" and y: "y = ys ! n" unfolding min_less_iff_conj by auto

  from n_len show "f x y = g x y" unfolding x y by (rule assms)
qed

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

(* TODO this should be a definition *)
abbreviation pad :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "pad n x xs \<equiv> xs @ x \<up> (n - length xs)"

lemma pad_length: "length (pad n x xs) = max n (length xs)" by simp
lemma pad_le_length[simp]: "length xs \<le> n \<Longrightarrow> length (pad n x xs) = n" by simp
lemma pad_ge_length[simp]: "length xs \<ge> n \<Longrightarrow> pad n x xs = xs" by simp

lemma pad_prefix: "prefix xs (pad n x xs)" by simp


(* TODO this should be a definition *)
abbreviation (input) ends_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" \<comment> \<open>an alternative to \<^const>\<open>last\<close>.\<close>
  where "ends_in x xs \<equiv> (\<exists>ys. xs = ys @ [x])"

lemma ends_inI[intro]: "ends_in x (xs @ [x])" by blast

lemma ends_in_Cons: "ends_in y (x # xs) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> ends_in y xs"
  by (simp add: Cons_eq_append_conv)

lemma ends_in_last: "xs \<noteq> [] \<Longrightarrow> ends_in x xs \<longleftrightarrow> last xs = x"
proof (intro iffI)
  assume "xs \<noteq> []" and "last xs = x"
  from \<open>xs \<noteq> []\<close> have "butlast xs @ [last xs] = xs"
    unfolding snoc_eq_iff_butlast by (intro conjI) auto
  then show "ends_in x xs" unfolding \<open>last xs = x\<close> by (intro exI) (rule sym)
qed \<comment> \<open>direction \<open>\<longrightarrow>\<close> by\<close> force

lemma ends_in_append: "ends_in x (xs @ ys) \<longleftrightarrow> (if ys = [] then ends_in x xs else ends_in x ys)"
proof (cases "ys = []")
  case False
  then have "xs @ ys \<noteq> []" by blast
  with ends_in_last have "ends_in x (xs @ ys) \<longleftrightarrow> last (xs @ ys) = x" .
  also have "... \<longleftrightarrow> last ys = x" unfolding \<open>ys \<noteq> []\<close>[THEN last_appendR] ..
  also have "... \<longleftrightarrow> ends_in x ys" using ends_in_last[symmetric] \<open>ys \<noteq> []\<close> .
  also have "... \<longleftrightarrow> (if ys = [] then ends_in x xs else ends_in x ys)" using \<open>ys \<noteq> []\<close> by simp
  finally show ?thesis .
qed \<comment> \<open>case \<open>ys = []\<close> by\<close> simp

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
  unfolding map_map comp_def using assms by (intro map_idI) fastforce

lemma map_map_inv_into_id:
  fixes f::"'a \<Rightarrow> 'b"
  assumes "inj_on f A"
      and "set bs \<subseteq> f ` A"
    shows "map f (map (inv_into A f) bs) = bs"
  unfolding map_map comp_def using assms by (intro map_idI) fastforce

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

subsection \<open>Trimming words\<close>

abbreviation "trimLeft b xs \<equiv> dropWhile (\<lambda>x. x = b) xs"
abbreviation "trimRight b xs \<equiv> rev (trimLeft b (rev xs))"
definition "trim b xs \<equiv> trimRight b (trimLeft b xs)"

lemma trim_nil[simp]: "trim b [] = []"
  unfolding trim_def by simp

lemma trim_left[simp]: "trim b (b # xs) = trim b xs"
  unfolding trim_def by simp

lemma trim_right[simp]: "trim b (xs @ [b]) = trim b xs"
  unfolding trim_def by (induction xs) auto

lemma trim_left_neq: "x \<noteq> b \<Longrightarrow> trim b (x # xs) = x # trimRight b xs"
  unfolding trim_def by (simp add: dropWhile_append3)

lemma trim_right_neq: "x \<noteq> b \<Longrightarrow> trim b (xs @ [x]) = trimLeft b xs @ [x]"
  unfolding trim_def by (simp add: dropWhile_append3)

lemma trim_rev: "trim b (rev xs) = rev (trim b xs)"
unfolding rev_is_rev_conv proof (induction xs)
  case (Cons x xs)
  then show ?case proof (cases "x = b")
    case True
    from True have 1: "trim b (rev (x # xs)) = trim b (rev xs)" by simp
    from True have 2: "rev (trim b (x # xs)) = rev (trim b xs)" by simp
    show ?thesis unfolding 1 2 by fact
  next
    case False
    have 1: "trim b (rev (x # xs)) = trimLeft b (rev xs) @ [x]"
      using trim_right_neq[OF False] by simp
    have 2: "rev (trim b (x # xs)) = trimLeft b (rev xs) @ [x]"
      using trim_left_neq[OF False] by simp
    show ?thesis unfolding 1 2 ..
  qed
qed simp

lemma trim_comm: "trimLeft b (trimRight b xs) = trimRight b (trimLeft b xs)"
  using trim_rev unfolding trim_def by fast

lemma trim_idem[simp]: "trim b (trim b xs) = trim b xs"
  unfolding trim_def trim_comm by simp

lemma trim_replicate[simp]: "trim b (b \<up> n) = []"
  by (induction n) auto

lemma trim_nil_set: "trim b xs = [] \<Longrightarrow> set xs \<subseteq> {b}"
proof (induction xs)
  case (Cons x xs)
  have "x = b" proof (rule ccontr)
    assume "x \<noteq> b"
    then have "trim b (x # xs) = x # trimRight b xs" by (rule trim_left_neq)
    with Cons(2) show False by simp
  qed
  with Cons show ?case by simp
qed simp

lemma trim_nil_eq: "trim b xs = [] \<longleftrightarrow> xs = b \<up> length xs"
proof
  assume "xs = b \<up> length xs"
  then obtain n where "xs = b \<up> n" ..
  thus "trim b xs = []" by simp
next
  assume "trim b xs = []"
  hence "set xs \<subseteq> {b}" by (rule trim_nil_set)
  then show "xs = b \<up> length xs" unfolding replicate_set_eq .
qed


lemma map_nthI:
  assumes f_nth: "\<And>n. n < length xs \<Longrightarrow> f n = xs ! n"
  shows "map f [0..<length xs] = xs"
proof -
  let ?is = "[0..<length xs]"
  from f_nth have "map f ?is = map (nth xs) ?is" by (intro list.map_cong0) simp
  also have "... = xs" unfolding map_nth ..
  finally show ?thesis .
qed


text\<open>A version of \<^const>\<open>nth\<close> with a default value; if the requested element is not in the list,
  the default value is returned instead.\<close>

definition nth_or :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a"
  where "nth_or x n xs \<equiv> if n < length xs then xs ! n else x"

lemma nth_or_simps[simp]:
  shows nth_or_Nil: "nth_or x n [] = x"
    and nth_or_val: "n < length xs \<Longrightarrow> nth_or x n xs = xs ! n"
    and nth_or_other: "\<not> n < length xs \<Longrightarrow> nth_or x n xs = x"
  unfolding nth_or_def by auto

lemma nth_or_map: "f (nth_or x n xs) = nth_or (f x) n (map f xs)" by (cases "n < length xs") auto

lemma nth_or_cases:
  assumes "n < length xs \<Longrightarrow> P (xs ! n)"
    and "\<not> (n < length xs) \<Longrightarrow> P x"
  shows "P (nth_or x n xs)"
  unfolding nth_or_def using assms by (fact ifI)


text\<open>Force a list to a given length; truncate if too long, and pad with the default value if too short.\<close>

definition take_or :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "take_or n x xs \<equiv> pad n x (take n xs)"

lemma take_or_length[simp]: "length (take_or n x xs) = n" unfolding take_or_def by force
lemma take_or_id: "length xs = n \<Longrightarrow> take_or n x xs = xs" unfolding take_or_def by simp

lemma take_or_altdef: "take_or n x xs = take n xs @ x \<up> (n - length xs)"
proof (cases "length xs \<ge> n")
  assume "length xs \<ge> n"
  then have "length (take n xs) \<ge> n" by simp
  with \<open>length xs \<ge> n\<close> show ?thesis unfolding take_or_def by force
next
  assume "\<not> length xs \<ge> n" hence "length xs < n" by simp
  then have *: "take n xs = xs" by simp
  show ?thesis unfolding take_or_def * ..
qed


text\<open>Force a list \<open>xs\<close> to match the length of another list \<open>ys\<close>;
  truncate if \<open>xs\<close> is longer than \<open>ys\<close>, insert corresponding values from \<open>ys\<close> if \<open>xs\<close> is shorter.
  Can also be interpreted as overwriting \<open>ys\<close> with values from \<open>xs\<close>;
  if \<open>xs\<close> is longer the additional values are ignored,
  if \<open>xs\<close> is shorter \<open>ys\<close> will retain some of its original values.\<close>

(* TODO find a more intuitive name *)
definition overwrite :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "overwrite xs ys \<equiv> take (length ys) xs @ drop (length xs) ys"

lemma overwrite_length: "length (overwrite xs ys) = length ys"
proof -
  let ?lx = "length xs" and ?ly = "length ys"
  have "length (overwrite xs ys) = min ?lx ?ly + (?ly - ?lx)" unfolding overwrite_def by simp
  also have "... = ?ly" by (cases "?ly \<ge> ?lx") auto
  finally show ?thesis .
qed

lemma overwrite_id: "length xs = length ys \<Longrightarrow> overwrite xs ys = xs" unfolding overwrite_def by simp
lemma overwrite_nth1: "n < min (length xs) (length ys) \<Longrightarrow> overwrite xs ys ! n = xs ! n"
  unfolding overwrite_def nth_append by simp

lemma overwrite_nth2:
  assumes "n < length ys"
    and "n \<ge> min (length xs) (length ys)"
  shows "overwrite xs ys ! n = ys ! n"
proof -
  let ?lx = "length xs" and ?ly = "length ys"
  from assms have "?lx \<le> ?ly" by linarith
  then have lm: "min ?lx ?ly = ?lx" by force
  then have lt: "length (take ?ly xs) = ?lx" by force
  from \<open>n \<ge> min ?lx ?ly\<close> have "n \<ge> ?lx" unfolding lm .

  from \<open>n \<ge> min ?lx ?ly\<close> have "\<not> n < length (take ?ly xs)" unfolding length_take by (rule leD)
  then have "overwrite xs ys ! n = drop ?lx ys ! (n - ?lx)"
    unfolding overwrite_def nth_append lt by presburger
  also have "... = ys ! n" unfolding nth_drop[OF \<open>?lx \<le> ?ly\<close>] le_add_diff_inverse[OF \<open>n \<ge> ?lx\<close>] ..
  finally show ?thesis .
qed

lemma overwrite_nth:
  assumes "n < length ys" \<comment> \<open>to ensure there is a \<^const>\<open>nth\<close> element.\<close>
  shows "overwrite xs ys ! n = (if n < min (length xs) (length ys) then xs ! n else ys ! n)"
proof (rule ifI)
  assume "n < min (length xs) (length ys)"
  thus "overwrite xs ys ! n = xs ! n" by (rule overwrite_nth1)
next
  assume "\<not> n < min (length xs) (length ys)"
  thus "overwrite xs ys ! n = ys ! n" by (intro overwrite_nth2[OF assms]) (rule leI)
qed

lemma finite_type_lists_length_le: "finite {xs::('s::finite list). length xs \<le> n}"
  using finite_lists_length_le[OF finite, of UNIV] by simp


subsubsection\<open>Almost Everywhere\<close>

text\<open>Analogous to \<^const>\<open>Ball\<close> and its notation \<^term>\<open>\<forall>x\<in>A. P\<close>.\<close>

abbreviation Alm_ball :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Alm_ball A P \<equiv> \<forall>\<^sub>\<infinity>x. x \<in> A \<longrightarrow> P x"
syntax
  "_Alm_ball" :: "pttrn \<Rightarrow> 's set \<Rightarrow> bool \<Rightarrow> bool"   ("(3\<forall>\<^sub>\<infinity>_/\<in>_./ _)" [0, 0, 10] 10)
translations
  "\<forall>\<^sub>\<infinity>x\<in>A. P" \<rightleftharpoons> "CONST Alm_ball A (\<lambda>x. P)"
print_translation\<open>[
  Syntax_Trans.preserve_binder_abs2_tr' \<^const_syntax>\<open>Alm_ball\<close> \<^syntax_const>\<open>_Alm_ball\<close>
]\<close> \<comment> \<open>to avoid eta-contraction of body (otherwise, \<^term>\<open>\<forall>\<^sub>\<infinity>x\<in>A. P x\<close> will be printed as \<^term>\<open>Alm_ball A P\<close>)\<close>


lemma ae_word_lengthI:
  fixes P :: "'s list \<Rightarrow> bool" and \<Sigma> :: "'s set"
  defines "P' w \<equiv> w \<in> \<Sigma>* \<longrightarrow> P w"
  assumes "finite \<Sigma>"
  assumes "\<And>w. w \<in> \<Sigma>* \<Longrightarrow> n \<le> length w \<Longrightarrow> P w"
  shows "\<forall>\<^sub>\<infinity>w. P' w"
proof -
  from assms(3) obtain n where n_def: "P' w" if "n \<le> length w" for w :: "'s list" unfolding P'_def by blast
  have "\<not> P' w \<longrightarrow> set w \<subseteq> \<Sigma> \<and> length w \<le> n" for w using n_def[of w] unfolding P'_def by force
  then have "{w. \<not> P' w} \<subseteq> {w. set w \<subseteq> \<Sigma> \<and> length w \<le> n}" by blast
  moreover from \<open>finite \<Sigma>\<close> have "finite {w. set w \<subseteq> \<Sigma> \<and> length w \<le> n}" by (fact finite_lists_length_le)
  ultimately show "\<forall>\<^sub>\<infinity>w. P' w" unfolding P'_def eventually_cofinite by (rule finite_subset)
qed

lemma ae_word_lengthE[elim?]:
  fixes P :: "'s list \<Rightarrow> bool" and \<Sigma> :: "'s set"
  defines "P' w \<equiv> w \<in> \<Sigma>* \<longrightarrow> P w"
  assumes "\<forall>\<^sub>\<infinity>w. P' w"
  obtains n where "\<And>w. w \<in> \<Sigma>* \<Longrightarrow> n \<le> length w \<Longrightarrow> P w"
proof (rule that, cases "{w. \<not> P' w} = {}")
  assume "{w. \<not> P' w} \<noteq> {}"
  define n where "n = Suc (Max (length ` {w. \<not> P' w}))"
  fix w assume "w \<in> \<Sigma>*" and "n \<le> length w"

  from \<open>\<forall>\<^sub>\<infinity>w. P' w\<close> have "finite {w. \<not> P' w}" unfolding eventually_cofinite .
  from \<open>length w \<ge> n\<close> have "length w > Max (length ` {w. \<not> P' w})"
    unfolding n_def by (fact Suc_le_lessD)
  then have "length w \<notin> length ` {w. \<not> P' w}"
    using \<open>{w. \<not> P' w} \<noteq> {}\<close> and \<open>finite {w. \<not> P' w}\<close> by (subst (asm) Max_less_iff) blast+
  then have "P' w" by blast
  with \<open>w \<in> \<Sigma>*\<close> show "P w" unfolding P'_def by blast
qed (use assms in blast)

lemma ae_word_length_iff:
  fixes P :: "'s list \<Rightarrow> bool"
  assumes "finite \<Sigma>"
  shows "(\<forall>\<^sub>\<infinity>w\<in>\<Sigma>*. P w) \<longleftrightarrow> (\<exists>n. \<forall>w\<in>\<Sigma>*. n \<le> length w \<longrightarrow> P w)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs" by (elim ae_word_lengthE) blast
next
  assume ?rhs
  then obtain n where "P w" if "w \<in> \<Sigma>*" and "n \<le> length w" for w by blast
  with \<open>finite \<Sigma>\<close> show ?lhs by (intro ae_word_lengthI)
qed


lemma ae_word_length_finite_iff:
  fixes P :: "'s::finite list \<Rightarrow> bool"
  shows "(\<forall>\<^sub>\<infinity>x. P x) \<longleftrightarrow> (\<exists>n. \<forall>w. n \<le> length w \<longrightarrow> P w)" (is "?lhs \<longleftrightarrow> ?rhs")
  using ae_word_length_iff[of UNIV P] by simp

lemma ae_word_length_finiteI:
  fixes P :: "'s::finite list \<Rightarrow> bool"
  assumes "\<And>w. n \<le> length w \<Longrightarrow> P w"
  shows "\<forall>\<^sub>\<infinity>x. P x"
  unfolding ae_word_length_finite_iff using assms by blast

lemma ae_word_length_finiteE[elim?]:
  fixes P :: "'s::finite list \<Rightarrow> bool"
  assumes "\<forall>\<^sub>\<infinity>x. P x"
  obtains n where "\<And>w. n \<le> length w \<Longrightarrow> P w"
  using assms unfolding ae_word_length_finite_iff by blast


lemma eventually_disj: "eventually P F \<or> eventually Q F \<Longrightarrow> eventually (\<lambda>x. P x \<or> Q x) F"
  by (elim disjE eventually_mono) blast+

(* TODO remove. these are fully subsumed by the rules used to prove them *)
lemma ae_conj_iff: "Alm_all (\<lambda>x. P x \<and> Q x) \<longleftrightarrow> Alm_all P \<and> Alm_all Q"
  by (rule eventually_conj_iff)

lemma ae_conjI:
  assumes "Alm_all P" "Alm_all Q"
  shows "Alm_all (\<lambda>x. P x \<and> Q x)"
using assms by (rule eventually_conj)


lemma list_all_last[elim]:
  assumes "list_all P xs"
    and "xs \<noteq> []"
  shows "P (last xs)"
  using assms by simp


end
