section\<open>Lists\<close>

theory Lists
  imports Main Misc
    "HOL-Library.More_List"
    "HOL-Library.Sublist"
    "HOL-Eisbach.Eisbach"
    "HOL-Library.Discrete_Functions"
begin

text\<open>Extends \<^theory>\<open>HOL.List\<close>.\<close>

lemma takeWhile_True[simp]: "takeWhile (\<lambda>x. True) = (\<lambda>x. x)" by fastforce


notation lists ("(_*)" [1000] 999) \<comment> \<open>Priorities taken from \<^const>\<open>rtrancl\<close>,
  to force parentheses on terms like \<^term>\<open>x \<in> (f A)*\<close>.
  Introducing an abbreviation would be nicer, since Ctrl+Click then shows the abbreviation,
  instead of directly jumping to \<^const>\<open>lists\<close>,
  but the abbreviation completely replaces references to \<^const>\<open>lists\<close>, which is confusing.\<close>
(*(* abbreviation (input) kleene_star ("(_*)" [1000] 999) where "\<Sigma>* \<equiv> lists \<Sigma>" *)

lemma lists_member[iff]: "xs \<in> X* \<longleftrightarrow> set xs \<subseteq> X" by blast

abbreviation replicate_exponent :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" (infixr "\<up>" 100)
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

lemma len_butlast_Cons: "xs \<noteq> [] \<Longrightarrow> length (butlast xs @ [x]) = length xs"
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

lemma inj_append_f:
  fixes xs ys :: "'a list" and f :: "'a list \<Rightarrow> 'b list" and g :: "'a list \<Rightarrow> 'b list"
  shows inj_append_L_fg: "inj f \<Longrightarrow> inj (\<lambda>xs. (f xs) @ (g ys))"
  and inj_append_R_fg: "inj g \<Longrightarrow> inj (\<lambda>ys. (f xs) @ (g ys))"
proof (rule injI)
  fix x y
  assume "f x @ g ys = f y @ g ys" and "inj f"
  thus "x = y" by (simp add: inj_eq)
next
  assume "inj g"
  thus "inj (\<lambda>ys. f xs @ g ys)" using injI by (simp add: inj_on_def)
qed

lemma infinite_lists:
  assumes "\<forall>l. \<exists>xs\<in>X. length xs \<ge> l"
  shows "infinite X"
proof -
  from assms have "\<nexists>n. \<forall>s\<in>X. length s < n" by (fold not_less) simp
  then show "infinite X" using finite_maxlen by (rule contrapos_nn)
qed


definition pad :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "pad n x xs \<equiv> xs @ x \<up> (n - length xs)"

lemma pad_length[simp]: "length (pad n x xs) = max n (length xs)" by (simp add: pad_def)
lemma pad_ge_length[simp]: "length xs \<ge> n \<Longrightarrow> pad n x xs = xs" by (simp add: pad_def)

lemma pad_prefix: "prefix xs (pad n x xs)" by (simp add: pad_def)


abbreviation (input) ends_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" \<comment> \<open>an alternative to \<^const>\<open>last\<close>.\<close>
  where "ends_in x xs \<equiv> (\<exists>ys. xs = ys @ [x])"

lemma ends_inI[intro?]: "ends_in x (xs @ [x])" by blast

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

lemma ends_in_drop[dest]:
  assumes "ends_in x xs"
    and "k < length xs"
  shows "ends_in x (drop k xs)"
  using assms by force

lemma Ball_set_map[iff?]: "set (map f xs) \<subseteq> A \<longleftrightarrow> (\<forall>x\<in>set xs. f x \<in> A)"
  unfolding set_map by (fact image_subset_iff)

abbreviation (input) starts_with :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" \<comment> \<open>an alternative to \<^const>\<open>last\<close>.\<close>
  where "starts_with x xs \<equiv> (\<exists>ys. xs = x # ys)"

lemma starts_withI[intro?]: "starts_with x (x # xs)" by blast

lemma starts_with_snoc: "starts_with y (xs @ [x]) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> starts_with y xs"
  by (simp add: append_eq_Cons_conv)

lemma starts_with_hd: "xs \<noteq> [] \<Longrightarrow> starts_with x xs \<longleftrightarrow> hd xs = x"
  apply auto
  using list.exhaust_sel by blast

lemma starts_with_append: "starts_with x (xs @ ys) \<longleftrightarrow> (if xs = [] then starts_with x ys else starts_with x xs)"
  apply (cases "xs = []")
   apply auto
  by (metis hd_append list.collapse list.sel(1))

lemma starts_rev [simp]: "starts_with x (rev l) \<longleftrightarrow> ends_in x l"
  using rev_swap by blast

lemma ends_rev [simp]: "ends_in x (rev l) \<longleftrightarrow> starts_with x l"
  by (induction l) simp_all

lemma starts_induct1: "P [x] \<Longrightarrow> (\<And>a xs. P (x # xs) \<Longrightarrow> P (x # a # xs)) \<Longrightarrow>
                      P (x # xs)" by (rule list.induct)

lemma starts_induct2: "starts_with x l \<Longrightarrow> P [x] \<Longrightarrow>
                       (\<And>a xs. P (x # xs) \<Longrightarrow> P (x # a # xs)) \<Longrightarrow> P l"
  apply (induction l)
  apply auto
  by (metis starts_induct1)

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

lemma trimRight_tl: "trimRight x (tl xs) = tl (trimRight x xs)"
  by (induction xs) (simp_all add: dropWhile_append)

lemma trimLeft_idem_app: "trimLeft x (trimLeft x xs1 @ xs2) = trimLeft x (xs1 @ xs2)"
  by (induction xs1) simp_all

lemma trimRight_idem_app: "trimRight x (xs1 @ trimRight x xs2) =
                           trimRight x (xs1 @ xs2)"
  by (induction xs1) (simp_all add: trimLeft_idem_app)

lemma map_nthI:
  assumes f_nth: "\<And>n. n < length xs \<Longrightarrow> f n = xs ! n"
  shows "map f [0..<length xs] = xs"
proof -
  let ?is = "[0..<length xs]"
  from f_nth have "map f ?is = map (nth xs) ?is" by (intro list.map_cong0) simp
  also have "... = xs" unfolding map_nth ..
  finally show ?thesis .
qed


declare nth_default_nth[simp]

lemma nth_default_cases:
  assumes "n < length xs \<Longrightarrow> P (xs ! n)"
    and "\<not> (n < length xs) \<Longrightarrow> P x"
  shows "P (nth_default x xs n)"
  unfolding nth_default_def using assms by (fact ifI)

lemma nth_default_split:
  "P (nth_default x xs n) \<longleftrightarrow> (n < length xs \<longrightarrow> P (xs ! n)) \<and> (\<not> (n < length xs) \<longrightarrow> P x)"
  unfolding nth_default_def by presburger

lemma nth_default_map[simp]: "nth_default (f dflt) (map f xs) n = f (nth_default dflt xs n)"
  by (rule nth_default_map_eq) (fact refl)



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
  show ?thesis unfolding take_or_def * pad_def ..
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


lemma Ball_set_last[dest]:
  assumes "\<forall>x\<in>set xs. P x"
    and "xs \<noteq> []"
  shows "P (last xs)"
  using assms by simp

lemmas list_all_last[elim] = Ball_set_last[folded list_all_iff]


subsection\<open>Split lists into chunks of \<open>n\<close> elements\<close>

fun chunks :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "chunks n [] = []"
| "chunks 0 xs = [xs]"
| "chunks n xs = (take n xs) # chunks n (drop n xs)"

lemmas chunks_induct = chunks.induct[params n and x xs and n x xs, case_names Nil 0 Split]
lemma chunks_cases[case_names Nil 0 Split]:
  fixes n :: nat and xs :: "'a list"
  obtains            "xs = []"
    |    x xs' where "xs = x # xs'" and "n = 0"
    | n' x xs' where "xs = x # xs'" and "n = Suc n'"
  by (cases "(n, xs)" rule: chunks.cases) blast+


lemma chunks_0[simp]: "xs \<noteq> [] \<Longrightarrow> chunks 0 xs = [xs]" by (induction xs) auto
lemma chunks_Split: "n > 0 \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> chunks n xs = (take n xs) # chunks n (drop n xs)"
  by (cases "(n, xs)" rule: chunks.cases) auto

lemma chunks_len_neq_Nil[dest]: "i < length (chunks n xs) \<Longrightarrow> xs \<noteq> []" by force

lemma concat_chunks: "concat (chunks n xs) = xs" by (induction rule: chunks.induct) auto

lemma length_chunks_not_dvd:
  assumes "xs \<noteq> []"
    and "\<not> n dvd length xs"
  shows "length (chunks n xs) = length xs div n + 1"
  using assms
proof (induction n xs rule: chunks_induct)
  case (Split n x xs)
  let ?n = "Suc n" and ?xs = "x # xs" let ?lxs = "length ?xs"
  show ?case
  proof (cases ?lxs ?n rule: linorder_cases)
    case greater
    then have ge: "?lxs \<ge> ?n" by (fact less_imp_le_nat)
    from greater have h1: "drop ?n ?xs \<noteq> []" by simp
    from ge and \<open>\<not> ?n dvd ?lxs\<close> have h2: "\<not> ?n dvd length (drop ?n ?xs)"
      unfolding length_drop by (subst less_eq_dvd_minus[symmetric]) auto

    note Split(1)[OF h1 h2, simplified, simp]
    have "length (chunks ?n ?xs) = Suc (Suc ((?lxs - ?n) div ?n))" by simp
    also from ge have "... = ?lxs div ?n + 1"
      using le_div_geq zero_less_Suc by presburger
    finally show ?thesis .
  next
    case less
    then have le: "?lxs \<le> ?n" by (fact less_imp_le_nat)
    then have "length (chunks ?n ?xs) = 1" by simp
    also from less have "... = ?lxs div ?n + 1" by simp
    finally show ?thesis .
  next
    case equal
    with \<open>\<not> ?n dvd ?lxs\<close> show ?thesis by simp
  qed
qed simp_all

lemma length_chunks_dvd:
  assumes "n dvd length xs"
  shows "length (chunks n xs) = length xs div n"
  using assms
proof (induction n xs rule: chunks_induct)
  case (Split n x xs)
  let ?n = "Suc n" and ?xs = "x # xs" let ?lxs = "length ?xs"
  show ?case
  proof (cases ?lxs ?n rule: linorder_cases)
    case greater
    then have ge: "?lxs \<ge> ?n" by (fact less_imp_le_nat)
    from ge and \<open>?n dvd ?lxs\<close> have h2: "?n dvd length (drop ?n ?xs)"
      unfolding length_drop by (subst less_eq_dvd_minus[symmetric]) auto

    note Split(1)[OF h2, simplified, simp]
    have "length (chunks ?n ?xs) = Suc ((?lxs - ?n) div ?n)" by simp
    also from ge have "... = ?lxs div ?n" by (simp add: le_div_geq)
    finally show ?thesis .
  next
    case less
    then have "\<not> ?n dvd ?lxs" using nat_dvd_not_less by simp
    with \<open>?n dvd ?lxs\<close> show ?thesis by contradiction
  next
    case equal
    then show ?thesis by simp
  qed
qed simp_all

lemma length_chunks: "length (chunks n xs) = length xs div n + (if xs = [] \<or> n dvd length xs then 0 else 1)"
proof (induction rule: ifI)
  case True   with length_chunks_dvd     show ?case by auto  next
  case False  with length_chunks_not_dvd show ?case by blast
qed

corollary length_chunks_bounds:
  shows "length (chunks n xs) \<ge> length xs div n"
    and "length (chunks n xs) \<le> length xs div n + 1"
  unfolding length_chunks by (rule ifI; linarith)+


lemma chunks_drop1[simp]: "n > 0 \<Longrightarrow> chunks n (drop n xs) = drop 1 (chunks n xs)"
  by (cases "(n, xs)" rule: chunks.cases) simp_all

lemma chunks_drop[simp]:
  assumes "n > 0"
  shows "chunks n (drop (n * i) xs) = drop i (chunks n xs)"
proof (induction i)
  case (Suc i)
  have "chunks n (drop (n * Suc i) xs) = chunks n (drop n (drop (n * i) xs))" by simp
  also from \<open>n > 0\<close> have "... = drop 1 (chunks n (drop (n * i) xs))" by (fact chunks_drop1)
  also have "... = drop (Suc i) (chunks n xs)" unfolding Suc.IH by simp
  finally show ?case .
qed simp


lemma div_times_less:
  fixes n l ::  nat
  assumes "\<not> n dvd l"
    and "l \<noteq> 0"
  shows "l div n * n < l"
  using assms by (metis dvd_triv_right less_mult_imp_div_less nat_neq_iff) (* TODO understand wtf happens here *)

lemma nth_chunks_helper:
  assumes "n > 0"
    and "i < length (chunks n xs)"
  shows "n * i < length xs"
proof (cases "n dvd length xs")
  assume "n dvd length xs"
  then have "length (chunks n xs) = length xs div n" by (fact length_chunks_dvd)
  with \<open>i < length (chunks n xs)\<close> have "i < length xs div n" by argo
  with \<open>n > 0\<close> have "n * i < length xs div n * n" by simp
  also have "... \<le> length xs" by simp
  finally show "n * i < length xs" .
next
  from \<open>i < length (chunks n xs)\<close> have "xs \<noteq> []" by force
  moreover assume "\<not> n dvd length xs"
  ultimately have "length (chunks n xs) = length xs div n + 1" by (fact length_chunks_not_dvd)
  with \<open>i < length (chunks n xs)\<close> have "i \<le> length xs div n" by linarith
  then have "n * i \<le> length xs div n * n" by simp
  also from \<open>\<not> n dvd length xs\<close> and \<open>xs \<noteq> []\<close> have "... < length xs" by (intro div_times_less) blast+
  finally show "n * i < length xs" .
qed

lemma nth_chunks:
  assumes "n > 0"
    and "i < length (chunks n xs)"
  shows "chunks n xs ! i = take n (drop (n * i) xs)"
  using assms
proof (cases rule: chunks_cases[where n=n and xs=xs])
  case (Split n' x xs')
  from assms have "chunks n xs ! i = hd (chunks n (drop (n * i) xs))"
    by (simp only: hd_drop_conv_nth chunks_drop)
  also from \<open>n > 0\<close> have "... = take n (drop (n * i) xs)"
  proof (subst chunks_Split)
    from assms have "n * i < length xs" by (fact nth_chunks_helper)
    then show "drop (n * i) xs \<noteq> []" by simp
  qed (simp_all only: list.sel)
  finally show ?thesis .
qed force+


corollary chunks_length_le:
  assumes "n > 0"
    and "i < length (chunks n xs)"
  shows "length (chunks n xs ! i) \<le> n"
  unfolding nth_chunks[OF assms] length_take by (fact min.cobounded2)


lemma div_imp_mult_less:
  fixes a b c :: nat
  assumes "a < b div c"
  shows "a * c < b"
proof -
  have "c \<noteq> 0"
  proof (rule ccontr, unfold not_not)
    assume "c = 0"
    with \<open>a < b div c\<close> show False by simp
  qed

  with assms have "a * c < b div c * c" by simp
  also from \<open>c \<noteq> 0\<close> have "... \<le> b" by simp
  finally show ?thesis .
qed

lemma chunks_length_eq:
  assumes "n > 0"
    and "i < length xs div n"
  shows "length (chunks n xs ! i) = n"
proof -
  from \<open>i < length xs div n\<close> have "i < length (chunks n xs)" unfolding length_chunks by (fact trans_less_add1)
  with \<open>n > 0\<close> have "length (chunks n xs ! i) = length (take n (drop (n * i) xs))" by (simp only: nth_chunks)
  also have "... = n" unfolding length_take
  proof (rule min_absorb2)
    from \<open>i < length xs div n\<close> have "Suc i \<le> length xs div n" by (fact Suc_leI)
    with \<open>n > 0\<close> have "n * Suc i \<le> length xs" by (simp add: less_eq_div_iff_mult_less_eq mult.commute)
    then show "n \<le> length (drop (n * i) xs)" unfolding length_drop by (simp add: mult.commute)
  qed
  finally show ?thesis .
qed

lemma chunks_empty_iff [iff]: "chunks n xs = [] \<longleftrightarrow> xs = []"
  by (metis chunks.simps(1) concat_chunks)

lemma in_chunks_subset: "xs \<in> set (chunks n ys) \<Longrightarrow> set xs \<subseteq> set ys"
proof (induction ys rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case
    by (metis concat.simps(2) concat_append concat_chunks set_mono_sublist split_list
        sublist_def)
qed


(*definition map_indexed :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
  where "map_indexed f xs \<equiv> map2 f [0..<length xs] xs" *)

lemma length_1_hd_iff: "length l = Suc 0 \<longleftrightarrow> [hd l] = l"
proof auto
  assume "length l = Suc 0"
  thus "[hd l] = l"
    by (metis length_0_conv length_Suc_conv list.sel(1))
next
  assume "[hd l] = l"
  thus "length l = Suc 0"
    by (metis length_Cons list.size(3))
qed

lemma length_1_ex_iff: "length l = Suc 0 \<longleftrightarrow> (\<exists>x. [x] = l)"
  apply auto
  using length_1_hd_iff by auto

lemma length_1_ex1_iff: "length l = Suc 0 \<longleftrightarrow> (\<exists>!x. [x] = l)"
  using length_1_ex_iff by auto

lemma length_1_hd_last: "length l = Suc 0 \<Longrightarrow> hd l = last l"
  by (metis last.simps length_1_hd_iff)

lemma length_1_last_iff: "length l = Suc 0 \<Longrightarrow> [last l] = l"
proof -
  assume a: "length l = Suc 0"
  hence 1: "hd l = last l" by (rule length_1_hd_last)
  show "[last l] = l" using a unfolding 1 [symmetric] length_1_hd_iff .
qed

fun flatten :: "'a list list \<Rightarrow> 'a list" where
  "flatten [] = []" |
  "flatten (l#ll) = l@(flatten ll)"

abbreviation flat_map :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "flat_map f l \<equiv> flatten (map f l)"

lemma set_flatten: "set (flatten l) = \<Union>(set (map set l))"
  by (induction l) simp_all

lemma in_set_flatten_iff: "x \<in> set (flatten l) \<longleftrightarrow> (\<exists>s\<in>set l. x \<in> set s)"
  by (simp add: set_flatten)

lemma zeroth_is_head: "l \<noteq> [] \<Longrightarrow> l ! 0 = hd l"
  by (induction l) auto

lemma flatten_not_emptyD: "flatten l \<noteq> [] \<Longrightarrow> l \<noteq> []"
  by auto

lemma length_flatten_uniform: "(\<And>e. e \<in> set l \<Longrightarrow> length e = n) \<Longrightarrow>
      length (flatten l) = n * length l"
  by (induction l) simp_all

lemma flatten_first_nth: "(\<And>e. e \<in> set l \<Longrightarrow> length e = n) \<Longrightarrow> i < n \<Longrightarrow>
       flatten l \<noteq> [] \<Longrightarrow> flatten l ! i = l ! 0 ! i"
  apply (induction i)
  apply auto
   apply (metis bot_nat_0.not_eq_extremum flatten.elims flatten_not_emptyD hd_append2
      list.set_sel(1) list.size(3) nth_Cons_0 zeroth_is_head)
  by (metis flatten.elims flatten_not_emptyD list.set_sel(1) nth_Cons_0 nth_append
      zeroth_is_head)

lemma flatten_drop_uniform: "(\<And>e. e \<in> set l \<Longrightarrow> length e = n) \<Longrightarrow>
                             drop n (flatten l) = flatten (tl l)"
  by (induction l) simp_all

lemma flatten_drop_prod_uniform: "(\<And>e. e \<in> set l \<Longrightarrow> length e = n) \<Longrightarrow>
       drop (m * n) (flatten l) = flatten (drop m l)"
  apply (induction m)
proof auto
  fix m :: nat
  assume a1: "drop (m * n) (flatten l) = flatten (drop m l)" and
         a2: "\<And>e. e \<in> set l \<Longrightarrow> length e = n"
  have 1: "drop (n + m * n) (flatten l) = drop n (drop (m * n) (flatten l))"
    by simp
  show "drop (n + m * n) (flatten l) = flatten (drop (Suc m) l)" unfolding 1 a1
    by (metis (no_types, opaque_lifting) Nil_is_append_conv a2 drop_Nil drop_Suc
        flatten.elims flatten_drop_uniform in_set_dropD list.sel(3) tl_drop)
qed

lemma nth_flatten_uniform: "(\<And>e. e \<in> set l \<Longrightarrow> length e = n) \<Longrightarrow>
       flatten l \<noteq> [] \<Longrightarrow> n > 0 \<Longrightarrow> i < length (flatten l) \<Longrightarrow>
       flatten l ! i = l ! (i div n) ! (i mod n)"
  apply (induction i rule: full_nat_induct)
  apply auto
  unfolding atomize_all [symmetric] atomize_imp [symmetric]
proof -
  fix i :: nat
  assume a1: "\<And>m. Suc m \<le> i \<Longrightarrow> flatten l ! m = l ! (m div n) ! (m mod n)" and
         a2: "\<And>e. e \<in> set l \<Longrightarrow> length e = n" and a3: "flatten l \<noteq> []" and
         a4: "0 < n" and a5: "i < length (flatten l)"
  show "flatten l ! i = l ! (i div n) ! (i mod n)"
    apply (cases "i < n") apply auto
    using a2 a3 flatten_first_nth apply blast
  proof -
    assume a6: "\<not>i < n"
    have 1: "l ! (i div n) = (drop (i div n) l) ! 0"
      by (metis Groups.mult_ac(2) a2 a5 add.right_neutral length_flatten_uniform
          less_imp_le_nat less_mult_imp_div_less nth_drop)
    have 2: "i - (i div n * n) = i mod n"
      by (fact semiring_modulo_class.minus_div_mult_eq_mod)
    have 3: "drop ((i div n) * n) (flatten l) = flatten (drop (i div n) l)"
      by (rule flatten_drop_prod_uniform) (fact a2)
    hence 4: "flatten (drop (i div n) l) = drop ((i div n) * n) (flatten l)"
      by simp
    have 5: "flatten l ! i = drop (i div n * n) (flatten l) ! (i mod n)"
      using 2 by (metis a5 div_mod_decomp less_imp_diff_less less_imp_le_nat
          minus_mod_eq_div_mult nth_drop)
    show "flatten l ! i = l ! (i div n) ! (i mod n)" unfolding 1 5
      apply (rule flatten_first_nth [THEN subst])
         apply (rule a2)
         apply (erule in_set_dropD)
      using a4 mod_less_divisor apply blast
       apply (metis 3 a5 length_drop length_greater_0_conv less_imp_diff_less
          minus_mod_eq_div_mult zero_less_diff)
      using 3 by simp
  qed
qed

lemma flatten_concat [simp]: "flatten (l1@l2) = (flatten l1)@(flatten l2)"
  by (induction l1) simp_all

lemma flatten_take_prod_uniform: "(\<And>e. e \<in> set l \<Longrightarrow> length e = n) \<Longrightarrow>
       take (m * n) (flatten l) = flatten (take m l)"
apply (induction m arbitrary: n l)
proof auto
  fix m n :: nat and l :: "'a list list"
  assume a1: "\<And>n l. (\<And>e. e \<in> set l \<Longrightarrow> length e = n) \<Longrightarrow>
               take (m * n) (flatten l) = flatten (take m l)" and
         a2: "\<And>e. e \<in> set l \<Longrightarrow> length e = n"
  have set_take_eq_length: "\<And>t e. e \<in> set (take t l) \<Longrightarrow> length e = n"
    using a2 by (meson in_set_takeD)
  show "take (n + m * n) (flatten l) = flatten (take (Suc m) l)"
  proof (cases l)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a list)
    then show ?thesis
    proof (cases "m < length l")
      case True
      have 1: "take (n + m * n) (flatten l) =
               (take n (flatten l)) @ (take (m * n) (drop n (flatten l)))"
        by (rule take_add)
      have 2: "take (Suc m) l = hd l#(take m (tl l))" using Cons by simp
      have 3: "take (m * n) (drop n (flatten l)) = flatten (take m (tl l))"
        using Cons by (smt (verit, del_insts) a2 append_eq_append_conv
            append_is_Nil_conv append_take_drop_id flatten.simps(2) flatten_concat
            flatten_drop_prod_uniform flatten_drop_uniform list.sel(3)
            list.set_intros(2))
      show ?thesis unfolding 1 2 3 by (simp add: a2 local.Cons)
    next
      case False
      hence "flatten (take (Suc m) l) = flatten l" by simp
      then show ?thesis using Cons a1 a2 apply auto
        by (metis False dual_order.refl leI le_Suc_eq length_flatten_uniform
            list.sel(3) mult.commute mult_le_mono take_Suc_Cons take_all_iff) 
    qed
  qed
qed

lemma flat_map_singleton [simp]: "flat_map (\<lambda>x. [x]) l = l"
  by (induction l) simp_all

lemma flatten_is_concat: "flatten = concat"
proof
  fix xs :: "'a list list"
  show "flatten xs = concat xs"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case by simp
  qed
qed

lemma flatten_empty_iff: "flatten l = [] \<longleftrightarrow> l = [] \<or> (\<forall>l' \<in> set l. l' = [])"
  by (metis Nil_eq_concat_conv flatten_is_concat flatten_not_emptyD)

lemma flatten_empty_iff': "flatten l = [] \<longleftrightarrow> (\<exists>n. l = replicate n [])"
proof
  assume a1: "flatten l = []"
  thus "\<exists>n. l = [] \<up> n"
  proof (induction l)
    case Nil
    show ?case by (rule exI [where x=0]) simp
  next
    case (Cons a l)
    then obtain n :: nat where n_def: "l = [] \<up> n" by auto
    have 1: "a = []" using Cons(2) by simp
    show ?case unfolding n_def 1 apply (rule exI [where x="Suc n"])
      by simp
  qed
next
  assume "\<exists>n. l = [] \<up> n"
  then obtain n :: nat where l_def: "l = [] \<up> n" ..
  show "flatten l = []" unfolding l_def
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case by simp
  qed
qed

lemma map_subst: "n < length l \<Longrightarrow> P (f (l ! n)) \<Longrightarrow> P ((map f l) ! n)"
  by simp

lemma map2_subst: "n < length l1 \<Longrightarrow> n < length l2 \<Longrightarrow> P (f (l1 ! n) (l2 ! n)) \<Longrightarrow>
                   P ((map2 f l1 l2) ! n)"
  by simp

lemma map2_subst_rev: "P ((map2 f l1 l2) ! n) \<Longrightarrow> n < length l1 \<Longrightarrow> n < length l2 \<Longrightarrow>
                   P (f (l1 ! n) (l2 ! n))"
  by simp

lemma zip_subst: "n < length l1 \<Longrightarrow> n < length l2 \<Longrightarrow> P (l1 ! n, l2 ! n) \<Longrightarrow>
                  P ((zip l1 l2) ! n)" by simp

lemma zip_subst_rev: "P ((zip l1 l2) ! n) \<Longrightarrow> n < length l1 \<Longrightarrow> n < length l2 \<Longrightarrow>
                  P (l1 ! n, l2 ! n)" by simp

lemma length_1_hd_subst: "length l = Suc 0 \<Longrightarrow> P (hd l) \<Longrightarrow> n < length l \<Longrightarrow> P (l ! n)"
  by (metis length_1_hd_iff less_Suc0 nth_Cons_0)

lemma length_Suc0_not_empty [simp]: "Suc 0 \<le> length l \<longleftrightarrow> l \<noteq> []"
  by (auto simp add: Suc_leI)

lemma list_length_induct [consumes 1]: "length l \<ge> n \<Longrightarrow> (\<And>l. length l = n \<Longrightarrow> P l) \<Longrightarrow>
        (\<And>a l. length l \<ge> n \<Longrightarrow> P l \<Longrightarrow> P (a#l)) \<Longrightarrow> P l"
proof (induct l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by force
qed

(* legacy version *)
lemma list_length_induct': "(\<And>l. length l = n \<Longrightarrow> P l) \<Longrightarrow>
        (\<And>a l. length l \<ge> n \<Longrightarrow> P l \<Longrightarrow> P (a#l)) \<Longrightarrow> length l \<ge> n \<Longrightarrow> P l"
  by (rule list_length_induct)

lemma rev_butlast_is_tl_rev: "rev (butlast l) = tl (rev l)"
  by (induction l) auto

lemma rev_tl_is_butlast_rev: "rev (tl l) = butlast(rev l)"
  by (induction l) auto

lemma rev_ends_in_starts_with: "ends_in x (rev l) \<longleftrightarrow> starts_with x l"
  by (induction l) auto

lemma rev_starts_with_ends_in: "starts_with x (rev l) \<longleftrightarrow> ends_in x l"
  apply (induction l)
  apply auto
  by (metis rev.simps(2) rev_swap)+

lemma rev_drop_is_take [simp]: "rev (drop (length l - k) l) = take k (rev l)"
  by (induction l) (simp_all add: drop_Cons')

lemma rev_take_is_drop [simp]: "rev (take (length l - k) l) = drop k (rev l)"
  by (induction l) (simp_all add: take_Cons')

lemma take_rev_is_drop: "take (length l - k) (rev l) = rev (drop k l)"
  by (induction l) (simp_all add: rev_drop)

lemma take_is_drop_rev: "take (length l - k) l = rev (drop k (rev l))"
  apply (induction l)
   apply auto
  by (metis drop_append drop_rev length_Cons length_rev rev.simps(2)
      rev_append rev_rev_ident)

lemma rev_bijective [intro, simp]: "bij rev"
  by (simp add: involuntory_imp_bij)

lemma subset_tl: "set (x # xs) \<subseteq> s \<Longrightarrow> set xs \<subseteq> s"
  by simp

lemma subset_hd: "set (x # xs) \<subseteq> s \<Longrightarrow> x \<in> s"
  by simp

lemma map_hd_concat: "map hd (l @ [[x]]) = map hd l @ [x]"
  by simp

lemma take_suc_n_eq_imp_n_eq: "take (Suc n) l1 = take (Suc n) l2 \<Longrightarrow>
                               take n l1 = take n l2"
  apply (induction n)
  apply auto
  by (metis Suc_eq_plus1 add_diff_cancel_left' butlast_take le_Suc_eq not_less_eq_eq
      plus_1_eq_Suc self_append_conv take_add take_all take_drop)

lemma take_ge_eq: "n \<le> m \<Longrightarrow> take m l1 = take m l2 \<Longrightarrow> take n l1 = take n l2"
  apply (induction m rule: nat_induct_at_least)
  using take_suc_n_eq_imp_n_eq by auto

lemma take_add_eq: "take (n + x) l1 = take (n + x) l2 \<Longrightarrow> take n l1 = take n l2"
  using le_add1 take_ge_eq by blast

lemma length_take_minus_k: "length (take (length l - k) l) = length l - k"
  by simp

lemma zeroth_app_non_empty [simp]: "l \<noteq> [] \<Longrightarrow> (l @ xs) ! 0 = l ! 0"
  by (induction l) simp_all

lemma zeroth_app_empty [simp]: "l = [] \<Longrightarrow> (l @ xs) ! 0 = xs ! 0"
  by simp

fun map_indexed_n :: "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_indexed_n n f [] = []" |
  "map_indexed_n n f (x#xs) = (f n x) # (map_indexed_n (Suc n) f xs)"

lemma map_indexed_n_altdef: "map_indexed_n n f xs =
                             map (\<lambda>(i, x). f i x) (enumerate n xs)"
  by (induction xs arbitrary: n) simp_all

lemma map_indexed_n_simps[simp]:
  shows map_indexed_n_length: "length (map_indexed_n n f xs) = length xs" and
        map_indexed_n_id: "map_indexed_n n (\<lambda>_ x. x) xs = xs"
  by (induction xs arbitrary: n) simp_all

lemma nth_map_indexed_n[simp]: "i < length xs \<Longrightarrow>
  map_indexed_n n f xs ! i = f (i+n) (xs ! i)"
  apply (induction xs arbitrary: i n)
    using less_Suc_eq_0_disj by auto

definition map_indexed :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_indexed f l \<equiv> map_indexed_n 0 f l"

lemma map_indexed_altdef1: "map_indexed f xs = map (\<lambda>(i, x). f i x) (enumerate 0 xs)"
  unfolding map_indexed_def by (rule map_indexed_n_altdef)

lemma map_indexed_altdef2: "map_indexed f xs = map (\<lambda>i. f i (xs ! i)) [0..<length xs]"
proof -
  let ?is = "[0..<length xs]"
  have "map_indexed f xs = map2 f (map (\<lambda>i. i) ?is) (map (nth xs) ?is)"
    by (simp add: enumerate_eq_zip map_indexed_altdef1 map_nth)
  also have "... = map (\<lambda>i. f i (xs ! i)) ?is" by (fact map2_map_map)
  finally show ?thesis .
qed

lemma map_indexed_altdef3: "map_indexed f xs = map2 f [0..<length xs] xs"
  unfolding map_indexed_altdef1 by (simp add: enumerate_eq_zip)

lemma map_indexed_simps[simp]:
  shows map_indexed_length: "length (map_indexed f xs) = length xs" and
        map_indexed_id: "map_indexed (\<lambda>_ x. x) xs = xs"
  unfolding map_indexed_def by simp_all

lemma map_map_indexed: "map_indexed f (map_indexed g xs) = map_indexed (\<lambda>i x. f i (g i x)) xs"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = map (\<lambda>i. f i (map (\<lambda>i. g i (xs ! i)) [0..<length xs] ! i)) [0..<length xs]"
    unfolding map_indexed_altdef2 unfolding length_map length_upt minus_nat.diff_0 ..
  also have "... = ?rhs" unfolding map_indexed_altdef2 by (intro map_ext) fastforce
  finally show ?thesis .
qed

lemma set_map_indexed: "set (map_indexed f xs) = (\<lambda>(i, x). f i x) ` set (enumerate 0 xs)"
  unfolding map_indexed_altdef1 set_map ..

lemma nth_map_indexed [simp]: "i < length xs \<Longrightarrow> map_indexed f xs ! i = f i (xs ! i)"
  unfolding map_indexed_def by simp

definition swap_index :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "swap_index l m n \<equiv> map_indexed (\<lambda>i x. if i = m then
        l ! n else if i = n then l ! m else x) l"

lemma swap_same_index [simp]: "swap_index l n n = l"
  unfolding swap_index_def apply (induction l arbitrary: n)
  unfolding map_indexed_def using list_eq_iff_nth_eq by fastforce+

lemma swap_index_length [simp]: "length (swap_index l m n) = length l"
  unfolding swap_index_def by simp

lemma swap_index_m [simp]: "m < length l \<Longrightarrow> n < length l \<Longrightarrow>
                            swap_index l m n ! m = l ! n"
  unfolding swap_index_def by simp

lemma swap_index_n [simp]: "m < length l \<Longrightarrow> n < length l \<Longrightarrow>
                            swap_index l m n ! n = l ! m"
  unfolding swap_index_def by simp

lemma swap_index_other [simp]: "i < length l \<Longrightarrow> i \<noteq> m \<Longrightarrow> i \<noteq> n \<Longrightarrow>
                                swap_index l m n ! i = l ! i"
  unfolding swap_index_def by simp

lemma swap_index_swapped: "swap_index l m n = swap_index l n m"
  unfolding swap_index_def map_indexed_def apply (induction l)
   apply auto
  by (smt (verit, best) map_indexed_n_length nth_equalityI nth_map_indexed_n)+

lemma swap_index_empty [simp]: "swap_index [] m n = []"
  by (metis length_Suc0_not_empty swap_index_length)

lemma set_swap_index_eq [simp]: "m < length l \<Longrightarrow> n < length l \<Longrightarrow>
                                 set (swap_index l m n) = set l"
  apply (induction l arbitrary: m n)
  apply auto
    apply (smt (verit, del_insts) in_set_conv_nth length_Cons set_ConsD
      swap_index_length swap_index_n swap_index_other swap_index_swapped)
   apply (metis in_set_conv_nth length_Cons nth_Cons_0 swap_index_length swap_index_m
      swap_index_n swap_index_other zero_less_Suc)
  by (smt (verit, best) in_set_conv_nth insert_iff length_Cons list.set(2)
      swap_index_length swap_index_m swap_index_n swap_index_other)

lemma swap_index_same_values [simp]: "l ! m = l ! n \<Longrightarrow> swap_index l m n = l"
  apply (induction l arbitrary: m n)
  apply auto
  by (smt (verit, ccfv_SIG) nth_equalityI nth_map_indexed swap_index_def
      swap_index_length)

lemma double_swap_id [simp]: "m < length l \<Longrightarrow> n < length l \<Longrightarrow>
                              swap_index (swap_index l m n) m n = l"
  apply (induction l arbitrary: m n)
  unfolding swap_index_def apply auto
  by (smt (z3) length_Cons map_indexed_length nth_equalityI nth_map_indexed)

lemma take_replicate: "m \<le> n \<Longrightarrow> take m (replicate n a) = replicate m a"
  by simp

lemma swap_index_map: "m < length l \<Longrightarrow> n < length l \<Longrightarrow>
                       swap_index (map f l) m n = map f (swap_index l m n)"
  apply (auto intro!: nth_equalityI)
  by (metis length_map nth_map swap_index_m swap_index_n swap_index_other)

lemma swap_index_zip: "m < length (zip l1 l2) \<Longrightarrow> n < length (zip l1 l2) \<Longrightarrow>
     swap_index (zip l1 l2) m n = zip (swap_index l1 m n) (swap_index l2 m n)"
  apply (auto intro!: nth_equalityI)
  by (metis (no_types, lifting) length_zip min_less_iff_conj nth_zip swap_index_n
      swap_index_other swap_index_swapped)

lemma swap_index_nth_casesI: "i < length l \<Longrightarrow> (i = m \<Longrightarrow> P (l ! n)) \<Longrightarrow>
                           (i = n \<Longrightarrow> P (l ! m)) \<Longrightarrow>
       (i \<noteq> n \<Longrightarrow> i \<noteq> m \<Longrightarrow> P (l ! i)) \<Longrightarrow> P (swap_index l m n ! i)"
  by (simp add: swap_index_def)

lemma swap_index_take: "k < length l \<Longrightarrow> m < k \<Longrightarrow> n < k \<Longrightarrow>
       swap_index (take k l) m n = take k (swap_index l m n)"
  apply (auto intro!: nth_equalityI)
  by (smt (verit, ccfv_SIG) length_take min_less_iff_conj nth_take order_less_trans
      swap_index_m swap_index_n swap_index_other)

lemma swap_index_drop: "m < length l \<Longrightarrow> n < length l \<Longrightarrow> k \<le> m \<Longrightarrow> k \<le> n \<Longrightarrow>
                    swap_index (drop k l) (m - k) (n - k) = drop k (swap_index l m n)"
  apply (auto intro!: nth_equalityI)
  by (smt (verit, ccfv_threshold) add.commute add_diff_cancel_left'
      dual_order.strict_trans2 le_add_diff_inverse length_drop less_diff_conv
      less_imp_le_nat nth_drop swap_index_m swap_index_n swap_index_other)

lemma nth_map_upto [simp]: "i < n \<Longrightarrow> map f [0..<n] ! i = f i"
  by simp

lemma nth_map_indexed_upto [simp]: "i < n \<Longrightarrow> map_indexed f [0..<n] ! i = f i i"
  by simp

lemma zeroth_in_setI: "x \<in> set l \<Longrightarrow> l ! 0 \<in> set l"
  by (meson length_pos_if_in_set nth_mem)

lemma list_set_induct: "(\<And>a l. P l \<Longrightarrow> x \<in> set l \<Longrightarrow> P (a#l)) \<Longrightarrow>
       (\<And>l. P(x#l)) \<Longrightarrow> x \<in> set l \<Longrightarrow> P l"
  by (induction l) auto

lemma map_subst_rev: "P ((map f l) ! 0) \<Longrightarrow> length l > 0 \<Longrightarrow> P (f (l ! 0))"
  by simp

lemma tl_eq_only_Nil: "l = tl l \<Longrightarrow> l = []"
  by (metis Nitpick.size_list_simp(2) not_less_eq)

lemma tl_eqI: "l = [] \<Longrightarrow> l = tl l"
  by simp

lemma drop_consumes_first_append: "n \<ge> length l1 \<Longrightarrow>
   drop n (l1@l2) = drop (n - length l1) l2"
  by simp

lemma ends_in_induct [consumes 1, case_names Single Cons]: "ends_in a xs \<Longrightarrow> P [a] \<Longrightarrow>
           (\<And>x xs. P (xs@[a]) \<Longrightarrow> P(x#xs@[a])) \<Longrightarrow> P xs"
proof -
  have 1: "\<exists>ys. xs = ys @ [a] \<Longrightarrow> xs = [a] \<or> (\<exists>x ys. xs = x#ys@[a])"
    apply auto
    by (metis list.exhaust)
   show "ends_in a xs \<Longrightarrow> P [a] \<Longrightarrow> (\<And>x xs. P (xs@[a]) \<Longrightarrow> P(x#xs@[a])) \<Longrightarrow> P xs"
     apply (induction xs)
     apply auto
     by (metis Cons_eq_append_conv)
 qed

function group_2 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "group_2 d [] = []" |
  "group_2 d [x] = [[d, x]]" |
  "group_2 d (t@[e']@[e]) = group_2 d t @ [[e', e]]"
  apply auto
  by (metis append.assoc append_Cons append_Nil rev_exhaust)
termination by lexicographic_order

lemma flatten_group_2_even: "even (length l) \<Longrightarrow> flatten (group_2 d l) = l"
  apply (induction d l rule: group_2.induct)
    apply auto
  by (metis append_Cons append_Nil flatten.simps(1) flatten.simps(2)
      flatten_concat group_2.simps(3))

lemma flatten_group_2_odd: "odd (length l) \<Longrightarrow> flatten (group_2 d l) = d#l"
  apply (induction d l rule: group_2.induct)
    apply auto
  by (metis Cons_eq_appendI append_same_eq eq_Nil_appendI flatten.simps(2)
      flatten_concat group_2.simps(3))

lemma group_2_empty_iff [iff]: "group_2 d xs = [] \<longleftrightarrow> xs = []"
  apply (induction d xs rule: group_2.induct)
    apply auto
   apply (simp add: flatten_group_2_even flatten_not_emptyD)
  by (metis Nil_is_append_conv flatten_group_2_even flatten_group_2_odd
      flatten_not_emptyD list.distinct(1))

lemma even_group_2_Cons2: "even (length xs) \<Longrightarrow> group_2 d (a#b#xs) =
                           [a, b] # group_2 d xs"
  apply (induction d xs rule: group_2.induct)
    apply auto
   apply (metis append_Cons append_Nil group_2.simps(1) group_2.simps(3))
  by (smt (verit, ccfv_threshold) Cons_eq_append_conv group_2.simps(3))

lemma even_group_2_Cons1: "even (length xs) \<Longrightarrow> group_2 d (a#xs) =
                           [d, a]#group_2 d xs"
  apply (induction d xs rule: group_2.induct)
    apply auto
  by (metis append_Cons append_Nil group_2.simps(3))

lemma odd_group_2_Cons: "odd (length xs) \<Longrightarrow> group_2 d (a#b#xs) =
                         [d, a]#group_2 d (b#xs)"
  apply (induction xs rule: group_2.induct)
    apply auto
   apply (metis append_Cons append_Nil group_2.simps(1) group_2.simps(2)
      group_2.simps(3))
  by (metis append_Cons append_Nil group_2.simps(3))

lemma odd_group_2_Cons1: "odd (length xs) \<Longrightarrow> group_2 d (a#xs) =
                          [a, hd xs]#group_2 d (tl xs)"
  apply (induction xs rule: group_2.induct)
    apply auto
   apply (simp add: even_group_2_Cons2)
  by (metis append.left_neutral append_Cons gcd_nat.extremum group_2.simps(3)
      hd_append2 list.size(3) tl_append2)

lemma group_2_Cons_induct [case_names base1 base2 step_even step_odd]:
  fixes xs :: "'a list" and P :: "'a list \<Rightarrow> bool"
  assumes base1: "P []" and base2: "\<And>x. P [x]" and
          step_even: "\<And>a b xs. even (length xs) \<Longrightarrow> P xs \<Longrightarrow> P (a#b#xs)" and
          step_odd: "\<And>a b xs. odd (length xs) \<Longrightarrow> P xs \<Longrightarrow> P (a#b#xs)"
        shows "P xs"
  apply (cases "even (length xs)")
   apply (induction "length xs" arbitrary: xs rule: even_nat_induct)
    apply (auto simp add: base1)
   apply (smt (verit, ccfv_threshold) length_Suc_conv step_even)
  apply (induction "length xs" arbitrary: xs rule: odd_nat_induct)
  using base2 apply (metis length_1_hd_iff)
  by (smt (verit, best) Suc_length_conv step_odd)

lemma even_group_2_is_chunks: "even (length xs) \<Longrightarrow> group_2 d xs = chunks 2 xs"
  apply (induction xs rule: group_2_Cons_induct)
     apply (auto simp add: numeral_2_eq_2)
   apply (simp add: even_group_2_Cons2 numeral_2_eq_2)
  using even_Suc numeral_2_eq_2 by auto


lemma odd_group_2_is_chunks: "odd (length xs) \<Longrightarrow> group_2 d xs = chunks 2 (d#xs)"
  apply (induction xs rule: group_2_Cons_induct)
     apply (auto simp add: numeral_2_eq_2)
  using even_Suc_Suc_iff numeral_2_eq_2 apply auto[1]
proof -
  fix a b :: 'a and xs :: "'a list"
  assume a1: "\<not> Suc (Suc 0) dvd length xs" and
         a2: "group_2 d xs =
              (d # take (Suc 0) xs) # chunks (Suc (Suc 0)) (drop (Suc 0) xs)" and
         a3: "\<not> Suc (Suc 0) dvd Suc (Suc (length xs))"
  then obtain h :: 'a and t :: "'a list" where xs_def: "xs = h#t"
    by (metis dvd_0_right list.size(3) neq_Nil_conv)
  show "group_2 d (a # b # xs) =
        [d, a] # (b # take (Suc 0) xs) # chunks (Suc (Suc 0)) (drop (Suc 0) xs)"
    unfolding xs_def apply simp using a2
    by (metis a1 drop0 drop_Suc_Cons even_Suc even_group_2_Cons1 length_Cons
        list.sel(1) list.sel(3) numeral_2_eq_2 odd_group_2_Cons1 xs_def)
qed

lemma even_length_group_2: "even (length xs) \<Longrightarrow>
                            length (group_2 d xs) = length xs div 2"
  by (simp add: even_group_2_is_chunks length_chunks_dvd)

lemma odd_length_group_2: "odd (length xs) \<Longrightarrow>
                           length (group_2 d xs) = Suc (length xs div 2)"
  by (simp add: length_chunks_dvd odd_group_2_is_chunks)

lemma flatten_repl_repl [simp]: "flatten ((x \<up> n) \<up> k) = replicate (n * k) x"
  by (induction k) (simp_all add: replicate_add)

lemma flatten_group_2_eqD: "flatten (group_2 d xs) = xs \<Longrightarrow> even (length xs)"
  using flatten_group_2_odd by fastforce

lemma flatten_group_2_uneqD: "flatten (group_2 d xs) = d#xs \<Longrightarrow> odd (length xs)"
  using flatten_group_2_even by fastforce

lemma set_of_bounded_lists_finite [intro]: "finite S \<Longrightarrow>
                                            finite {w. length w \<le> n \<and> set w \<subseteq> S}"
  apply (subst conj_comms(1))
  apply (erule finite_lists_length_le)
  done

lemma length_group_2_rev [simp]: "length (group_2 d (rev xs)) = length (group_2 d xs)"
  apply (induction xs rule: group_2.induct)
    apply auto
  by (smt (verit) add_Suc_right even_length_group_2 length_Cons length_append
      length_rev list.size(3) list.size(4) odd_length_group_2)

lemma length_group_2_map [simp]: "length (group_2 d (map f xs)) =
                                  length (group_2 d xs)"
  apply (induction xs rule: group_2.induct)
    apply auto
  by (metis Cons_eq_append_conv group_2.simps(3) length_append_singleton)

lemma length_group_2 [simp]: "length (group_2 d xs) = (Suc (length xs)) div 2"
  apply (induction xs rule: group_2.induct)
    apply auto
  by (metis Cons_eq_appendI append_Nil group_2.simps(3) length_append_singleton)

lemma group_2_butlast_butlast: "group_2 d (butlast (butlast xs)) =
                                butlast (group_2 d xs)"
  apply (induction xs rule: group_2.induct)
    apply auto
  by (metis append.assoc append_Cons append_Nil butlast_snoc group_2.simps(3))

lemma even_length_tl_group_2: "even (length xs) \<Longrightarrow>
                               tl (group_2 d xs) = group_2 d (tl (tl xs))"
  by (smt (verit, del_insts) Nitpick.size_list_simp(2) even_Suc group_2_empty_iff
      list.collapse list.inject list.sel(2) odd_group_2_Cons1)

lemma odd_length_tl_group_2: "odd (length xs) \<Longrightarrow>
                              tl (group_2 d xs) = group_2 d (tl xs)"
  by (metis even_Suc even_group_2_is_chunks even_length_tl_group_2 length_Cons
      list.sel(3) odd_group_2_is_chunks)

lemma flatten_butlast: "xs \<noteq> [] \<Longrightarrow> flatten (butlast xs) =
                        (butlast ^^ (length (last xs))) (flatten xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a xs)
  have "xs = [] \<Longrightarrow> ?case" apply simp
    apply (rule sym)
    apply (induction a rule: rev_induct)
     apply auto
    unfolding funpow_swap1 by simp
  moreover have "xs \<noteq> [] \<Longrightarrow> ?case"
    apply (frule IH(1)) apply auto
    by (smt (verit, ccfv_threshold) Nat.add_diff_assoc append.simps(1)
        append_butlast_last_id append_eq_conv_conj butlast_power diff_add_inverse2
        diff_is_0_eq flatten.simps(2) flatten_concat leI length_append
        less_imp_le_nat self_append_conv take_add)
  ultimately show ?case by simp
qed

lemma starts_with_takeD: "starts_with x (take n xs) \<Longrightarrow> starts_with x xs"
  by (metis append_Cons append_take_drop_id)

function first_with_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "first_with_index P [] = 0" |
  "P h \<Longrightarrow> first_with_index P (h#t) = 0" |
  "\<not>P h \<Longrightarrow> first_with_index P (h#t) = Suc (first_with_index P t)"
  apply auto
  by (metis list.exhaust)
termination by lexicographic_order

lemma first_with_index_has_property: "i < length xs \<Longrightarrow> P (xs ! i) \<Longrightarrow>
                                      P (xs ! (first_with_index P xs))"
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a xs)
  then show ?case
    by (metis One_nat_def Suc_leI bot_nat_0.not_eq_extremum first_with_index.simps(2)
        first_with_index.simps(3) less_diff_conv2 list.size(4) nth_Cons' nth_Cons_Suc)
qed

lemma first_with_index_least_index:
  fixes xs :: "'a list" and i :: nat
  assumes "i < length xs" and
          "P (xs ! i)"
        shows "first_with_index P xs \<le> i"
  using assms
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a xs)
  have "P a \<Longrightarrow> ?case" by simp
  moreover have "\<not>P a \<Longrightarrow> i = 0 \<Longrightarrow> ?case" using IH by simp
  moreover have "\<not>P a \<Longrightarrow> i > 0 \<Longrightarrow> ?case" using IH
    by (metis Suc_diff_1 add_le_cancel_left first_with_index.simps(3)
        length_Cons nat_add_left_cancel_less nth_Cons_Suc plus_1_eq_Suc)
  ultimately show ?case by blast
qed

lemma first_with_index_upper_bound: "first_with_index P xs \<le> length xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases "P a") simp_all
qed

lemma first_with_index_none: "(\<And>i. i < length xs \<Longrightarrow> \<not>P (xs ! i)) \<Longrightarrow>
                              first_with_index P xs = length xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (metis Suc_mono first_with_index.simps(3) length_Cons nth_Cons_0 nth_Cons_Suc
        zero_less_Suc)
qed

lemma first_with_index_app1: "i < length xs \<Longrightarrow> P (xs ! i) \<Longrightarrow>
                              first_with_index P (xs @ ys) = first_with_index P xs"
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a xs)
  then show ?case
    by (metis append_Cons first_with_index.simps(2) first_with_index.simps(3)
        first_with_index_least_index first_with_index_none leD length_Cons)
qed

lemma first_with_index_app2: "(\<And>i. i < length xs \<Longrightarrow> \<not>P (xs ! i)) \<Longrightarrow>
                              first_with_index P (xs @ ys) =
                              first_with_index P ys + length xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (metis Suc_le_eq add_Suc_right append_Cons first_with_index.simps(3)
        length_Cons less_Suc_eq_le nth_Cons_0 nth_Cons_Suc zero_less_Suc)
qed

definition last_with_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "last_with_index P xs \<equiv> length xs - first_with_index P (rev xs) - 1"

lemma last_with_index_has_property: "i < length xs \<Longrightarrow> P (xs ! i) \<Longrightarrow>
                                      P (xs ! (last_with_index P xs))"
proof -
  assume a1: "i < length xs" and a2: "P (xs ! i)"
  have 1: "length xs - i - 1 < length (rev xs)" using a1 by simp
  have 2: "P ((rev xs) ! (length xs - i - 1))" using a2 apply simp
    by (metis a1 length_rev rev_nth rev_rev_ident)
  note first_with_index_has_property [OF 1, of P, OF 2]
  thus "P (xs ! last_with_index P xs)" unfolding last_with_index_def
    by (metis 1 2 diff_diff_cancel diff_diff_left diff_right_commute
        first_with_index_least_index length_rev less_imp_diff_less plus_1_eq_Suc rev_nth)
qed

lemma last_with_index_greatest_index:
  fixes xs :: "'a list" and i :: nat
  assumes "i < length xs" and
          "P (xs ! i)"
        shows "last_with_index P xs \<ge> i"
  using first_with_index_least_index [of "length xs - i - 1" "rev xs" P]
  unfolding last_with_index_def using assms
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred bot_nat_0.not_eq_extremum
      diff_diff_cancel diff_right_commute length_rev linorder_le_less_linear nless_le
      rev_nth zero_less_diff)

lemma last_with_index_within_bounds:
  fixes xs :: "'a list" and i :: nat
  assumes "i < length xs" and
          "P (xs ! i)"
        shows "last_with_index P xs < length xs"
  using first_with_index_least_index [of "length xs - i - 1" "rev xs" P]
  unfolding last_with_index_def using assms by linarith

lemma last_with_index_upper_bound: "last_with_index P xs \<le> length xs"
  unfolding last_with_index_def
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases "P a") simp_all
qed

lemma last_with_index_none: "(\<And>i. i < length xs \<Longrightarrow> \<not>P (xs ! i)) \<Longrightarrow>
                             last_with_index P xs = 0"
  unfolding last_with_index_def using first_with_index_none
  by (metis One_nat_def Suc_pred bot_nat_0.not_eq_extremum diff_diff_left
      diff_less_Suc length_rev not_less_iff_gr_or_eq plus_1_eq_Suc rev_nth zero_less_diff)

lemma last_with_index_Nil [simp]: "last_with_index P [] = 0"
  unfolding last_with_index_def by simp

lemma last_with_index_Cons1: "i < length t \<Longrightarrow> P (t ! i) \<Longrightarrow>
                             last_with_index P (h#t) = Suc (last_with_index P t)"
  unfolding last_with_index_def apply auto
  apply (subst first_with_index_app1 [where i="length t - i - 1"])
    apply auto
   apply (simp add: rev_nth)
  by (smt (verit, del_insts) Suc_diff_Suc diff_diff_cancel first_with_index_least_index
      length_rev less_imp_diff_less not_less_eq rev_nth rev_rev_ident)

lemma last_with_index_Cons2: "(\<And>i. i < length t \<Longrightarrow> \<not>P (t ! i)) \<Longrightarrow>
                              last_with_index P (h#t) = 0"
  unfolding last_with_index_def apply auto
  apply (cases "P h")
   apply (subst first_with_index_app2)
    apply auto
   apply (simp add: rev_nth)
  apply (subst first_with_index_app2)
   apply auto
  by (simp add: rev_nth)

lemma last_with_index_app1: "i < length ys \<Longrightarrow> P (ys ! i) \<Longrightarrow> last_with_index P (xs @ ys) =
                             last_with_index P ys + length xs"
  unfolding last_with_index_def apply simp
  apply (subst first_with_index_app1 [where i="length ys - i - 1"])
    apply auto
   apply (simp add: rev_nth)
proof -
  assume a1: "i < length ys" and a2: "P (ys ! i)"
  have "first_with_index P (rev ys) < length ys" using a1 a2
    by (metis first_with_index_least_index first_with_index_upper_bound in_set_conv_nth
        leD length_rev nless_le set_rev)
  thus "length xs + length ys - Suc (first_with_index P (rev ys)) =
        length ys - Suc (first_with_index P (rev ys)) + length xs" by (simp add: add.commute)
qed

lemma last_with_index_app2: "(\<And>i. i < length ys \<Longrightarrow> \<not>P (ys ! i)) \<Longrightarrow>
                             last_with_index P (xs @ ys) = last_with_index P xs"
  unfolding last_with_index_def apply simp
  apply (subst first_with_index_app2)
   apply auto
  by (simp add: rev_nth)

lemma star_subset_iff [iff]: "(S1)* \<subseteq> (S2)* \<longleftrightarrow> S1 \<subseteq> S2"
  by auto (metis lists.simps listsE subset_iff)

lemma tl_zip: "tl (zip l1 l2) = zip (tl l1) (tl l2)"
  by (metis (no_types, lifting) list.collapse list.sel(3) tl_Nil zip_Cons_Cons
      zip_eq_Nil_iff)

lemma prefix_take_iff: "prefix xs ys \<longleftrightarrow> take (length xs) ys = xs"
  by (metis append_eq_conv_conj prefix_def)

lemmas list_length_full_induct = measure_induct_rule [where f=length]

lemma those_Some_map_the: "None \<notin> set xs \<Longrightarrow> those xs = Some (map the xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a) simp_all
qed

lemma map_takeWhile: "map f (takeWhile (\<lambda>x. P (f x)) xs) = takeWhile P (map f xs)"
  by (induction xs) simp_all

lemma nth_equalityI': "length xs = length ys \<Longrightarrow>
                       (\<And>i. i < length xs \<Longrightarrow> length xs = length ys \<Longrightarrow> xs ! i = ys ! i) \<Longrightarrow>
                       xs = ys"
  by (rule nth_equalityI)

lemma trimRight_replicate_right: "x \<notin> set xs \<Longrightarrow> \<exists>n. trimRight x (xs@(replicate n x)) = xs"
  by (metis (mono_tags, lifting) append.right_neutral dropWhile_eq_self_iff
      last_in_set last_rev replicate_0 rev.simps(1) rev_rev_ident)

lemma star_not_empty [simp]: "S* \<noteq> {}" by blast

lemma list_only_one_different_element:
  fixes xs :: "'a list" and x y :: 'a
  assumes "\<exists>!i. i < length xs \<and> xs ! i = x" and
          "set xs \<subseteq> {x, y}"
        obtains k l :: nat where "xs = (replicate k y) @ [x] @ (replicate l y)" using assms
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case IH: (Cons a xs)
  then obtain i :: nat where i_lt: "i < length (a # xs)" and i_nth: "(a # xs) ! i = x"
    by blast
  show ?case
  proof (cases i)
    case 0
    show ?thesis apply (rule IH(2) [of 0 "length xs"])
      using i_lt i_nth IH(3, 4) unfolding 0 apply auto
      by (metis Suc_mono in_set_conv_nth nth_Cons_0 nth_Cons_Suc replicate_set_eq
          subset_insert zero_less_Suc)
  next
    case (Suc n)
    show ?thesis
    proof (rule IH(1), rule IH(2))
      fix k l :: nat
      assume "xs = y \<up> k @ [x] @ y \<up> l"
      thus "a # xs = y \<up> (Suc k) @ [x] @ y \<up> l" using IH(3, 4)
        by (metis Suc append_Cons i_lt i_nth insert_iff length_greater_0_conv list.size(3)
            not_less_zero nth_Cons_0 old.nat.distinct(1) replicate_Suc singletonD subset_hd)
    next
      show "\<exists>!i. i < length xs \<and> xs ! i = x"
        apply (rule ex1I [where a=n])
        using i_lt i_nth unfolding Suc apply auto
        by (metis IH.prems(2) Suc_mono length_Cons nat.inject nth_Cons_Suc)
    next
      show "set xs \<subseteq> {x, y}" using IH(4) by auto
    qed
  qed
qed

definition take_every_nth :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "take_every_nth n xs \<equiv> if xs = [] then [] else map hd (chunks n xs)"

lemma length_take_every_nth: "n > 0 \<Longrightarrow> length (take_every_nth n xs) =
                              nat (ceiling (length xs / n))"
  unfolding take_every_nth_def apply auto
proof (induction n xs rule: chunks_induct)
  case (Nil n)
  then show ?case by simp
next
  case (0 x xs)
  then show ?case by simp
next
  case (Split n x xs)
  then show ?case apply auto
    apply (cases "length xs \<le> n")
     apply auto
     apply (smt (verit) ceiling_le_one ceiling_le_zero less_divide_eq_1_pos nat_1
        of_nat_0_le_iff of_nat_le_iff zero_less_divide_iff)
  proof -
    assume a1: "length (chunks (Suc n) (drop n xs)) =
                nat \<lceil>(real (length xs) - real n) / (1 + real n)\<rceil>" and
           a2: "\<not> length xs \<le> n"
    have 1: "length xs > n" using a2 by simp
    have "Suc (nat \<lceil>(real (length xs) - real n) / (1 + real n)\<rceil>) =
          nat (\<lceil>(real (length xs) - real n) / (1 + real n)\<rceil> + 1)" using 1
      by (smt (verit) Suc_nat_eq_nat_zadd1 ceiling_le_zero less_imp_of_nat_less
          of_nat_0_le_iff zero_less_divide_iff)
    also have "... = nat (\<lceil>(real (length xs) - real n) / (1 + real n) + 1\<rceil>)" by simp
    also have "... = nat (\<lceil>((real (length xs) - real n) + (1 + real n)) / (1 + real n)\<rceil>)"
      apply (subst add_divide_distrib)
      by simp
    also have "... = nat (\<lceil>(real (length xs) + 1) / (1 + real n)\<rceil>)" by simp
    also have "... = nat (\<lceil>(1 + real (length xs)) / (1 + real n)\<rceil>)"
      apply (subst add.commute)
      ..
    finally show "Suc (nat \<lceil>(real (length xs) - real n) / (1 + real n)\<rceil>) =
                  nat \<lceil>(1 + real (length xs)) / (1 + real n)\<rceil>" .
  qed
qed

lemma take_every_nth_nth: "i < length xs \<Longrightarrow> n dvd i \<Longrightarrow>
                           take_every_nth n xs ! (i div n) = xs ! i"
  unfolding take_every_nth_def apply auto
proof (induction n xs arbitrary: i rule: chunks_induct)
  case (Nil n)
  then show ?case by simp
next
  case (0 x xs)
  then show ?case by simp
next
  case (Split n x xs)
  define j :: nat where "j \<equiv> i - Suc n"
  show ?case
  proof (cases "Suc n \<le> i")
    case True
    hence 3: "drop n xs \<noteq> []" using Split(2) by simp
    show ?thesis using True apply simp
      apply (subst nth_Cons)
      apply (cases "i div Suc n")
       apply auto
      using div_greater_zero_iff not_gr_zero apply blast
      apply (subst nth_map)
      using length_take_every_nth [unfolded take_every_nth_def, of "Suc n" "drop n xs"]
          3 apply simp
    proof -
      fix k :: nat
      have 1: "real (length xs) - real n = real (length xs - n)" using 3 by auto
      assume a1: "i div Suc n = Suc k"
      hence "i div Suc n \<le> length xs div Suc n" using Split(2)
        by (metis Suc_le_mono div_le_mono length_Cons less_eq_Suc_le)
      hence "k < length xs div Suc n" using a1 by simp
      hence "k < nat \<lfloor>length xs / (n + 1)\<rfloor>"
        by (metis Suc_eq_plus1 floor_divide_of_nat_eq nat_int)
      moreover have "\<lfloor>length xs / (n + 1)\<rfloor> \<le> \<lceil>(real (length xs) - real n) / (1 + real n)\<rceil>"
        unfolding 1 ceiling_div_is_floor_div apply simp
        by (smt (verit) 1 ceiling_div_is_floor_div of_nat_Suc)
      ultimately show "k < Int.nat \<lceil>(real (length xs) - real n) / (1 + real n)\<rceil>" by simp
    next
      fix k :: nat
      assume a1: "Suc n \<le> i" and
             a2: "i div Suc n = Suc k"
      have 1: "k = i div Suc n - 1" using a2 by simp
      have 2: "k = (i - Suc n) div Suc n" unfolding 1
        using a1 diff_Suc_1 le_div_geq zero_less_Suc by presburger
      have 3: "map hd (chunks (Suc n) (drop n xs)) ! ((i - Suc n) div Suc n) =
               hd ((chunks (Suc n) (drop n xs)) ! ((i - Suc n) div Suc n))"
        apply (subst nth_map)
         apply auto
        unfolding length_chunks apply auto
        using 3 apply fastforce
         apply (metis Nat.diff_cancel Nitpick.size_list_simp(2) Split.prems(1,2,3) a1
            diff_less_mono dvd_mult_div_cancel less_eq_dvd_minus list.sel(3)
            nat_mult_less_cancel_disj plus_1_eq_Suc)
        by (metis Nat.diff_cancel Split.prems(1) a1 diff_less_mono div_le_mono
            le_imp_less_Suc length_Cons nat_less_le plus_1_eq_Suc)
      show "hd (chunks (Suc n) (drop n xs) ! k) = xs ! (i - Suc 0)" unfolding 2
        apply (subst Split.IH [simplified, of "i - Suc n", unfolded 3])
           apply auto
           apply (metis Split.prems(1) a1 diff_Suc_Suc diff_less_mono length_Cons)
          apply (simp add: Split.prems(2))
        using Split.prems(1) a1 by auto
    qed
  next
    case False
    then show ?thesis apply simp
      using Split(3)
      by (metis Euclidean_Rings.div_eq_0_iff dvd_div_eq_0_iff linorder_not_less nth_Cons_0)
  qed
qed

lemma take_every_nth_empty_iff [iff]: "take_every_nth n xs = [] \<longleftrightarrow> xs = []"
  unfolding take_every_nth_def by simp

lemma take_every_nth_length_helper: "nat (ceiling (length xs / n)) =
                                     (length xs + n - 1) div n"
  by (smt (verit, best) One_nat_def ceiling_div_is_floor_div diff_divide_distrib
      floor_divide_of_nat_eq length_Suc0_not_empty
      linordered_euclidean_semiring_class.of_nat_div list.size(3) nat_div_as_int of_nat_0
      of_nat_1 of_nat_add of_nat_diff_if trans_le_add1)

lemma take_every_nth_altdef: "n > 0 \<Longrightarrow> take_every_nth n xs =
       map (\<lambda>i. xs ! (i * n)) [0..<(length xs + n - 1) div n]"
  apply (rule nth_equalityI)
   apply auto
   apply (erule length_take_every_nth [unfolded take_every_nth_length_helper, simplified])
  unfolding length_take_every_nth take_every_nth_length_helper [simplified, symmetric]
proof auto
  fix i :: nat
  assume a1: "0 < n" and a2: "i < nat \<lceil>real (length xs) / real n\<rceil>"
  show "take_every_nth n xs ! i = xs ! (i * n)"
    using take_every_nth_nth [of "i * n" xs n] a2 apply auto
    by (smt (verit) a1 linorder_not_less nat_ceiling_le_eq of_nat_0 of_nat_less_iff
        of_nat_mult pos_less_divide_eq)
qed

lemma take_every_nth_0_Cons [simp]: "take_every_nth 0 (h#t) = [h]"
  unfolding take_every_nth_def by simp

lemma take_every_nth_empty [simp]: "take_every_nth n [] = []"
  by simp

lemma hd_map2: "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> hd (map2 f xs ys) = f (hd xs) (hd ys)"
  by (simp add: hd_zip list.map_sel(1))

lemma tl_map2: "tl (map2 f xs ys) = map2 f (tl xs) (tl ys)"
  by (metis map_tl tl_zip)

lemma nth_ConsI: "(n = 0 \<Longrightarrow> P h) \<Longrightarrow> (n > 0 \<Longrightarrow> P (t ! (n - 1))) \<Longrightarrow> P ((h#t) ! n)"
  unfolding nth_Cons by (cases n) simp_all

lemma chunks_replicate_append: "n > 0 \<Longrightarrow> chunks n ((replicate n x)@xs) =
                                (replicate n x)#chunks n xs"
  apply (induction n xs rule: chunks_induct)
    apply auto
  by (smt (verit, best) Lists.take_replicate Suc_diff_Suc Suc_pred chunks.elims
      chunks.simps(1) diff_diff_cancel drop_replicate nat_less_le order.refl
      replicate_empty)

lemma chunks_length_n_append: "n > 0 \<Longrightarrow> length xs = n \<Longrightarrow>
                               chunks n (xs@ys) = xs#chunks n ys"
  by (induction n xs rule: chunks_induct) simp_all

lemma list_take_rev_Cons: "n < length xs \<Longrightarrow>
                           (xs ! n)#(rev (take n xs)) = rev (take (Suc n) xs)"
  by (simp add: take_Suc_conv_app_nth)

lemma set_listE: "x \<in> set xs \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> xs ! i = x \<Longrightarrow> P) \<Longrightarrow> P"
  by (meson in_set_conv_nth)

lemma last_map2: "length l1 = length l2 \<Longrightarrow> l1 \<noteq> [] \<Longrightarrow> last (map2 f l1 l2) = f (last l1) (last l2)"
  by (metis last_map last_zip length_0_conv old.prod.case zip_eq_Nil_iff)

lemma set_tl_subset: "set (tl l) \<subseteq> set l"
  by (cases l) auto

lemma set_list_eq_singleton_iff: "set xs = {x} \<longleftrightarrow> (\<exists>k>0. xs = replicate k x)"
  by (metis replicate_set_eq set_replicate_iff subsetI)

lemma length_takeWhile_eq: "k < length xs \<Longrightarrow> (\<And>n. n < k \<Longrightarrow> P (xs ! n)) \<Longrightarrow> \<not>P (xs ! k) \<Longrightarrow>
                            length (takeWhile P xs) = k"
  by (metis length_takeWhile_less_P_nth nat_less_le nth_mem set_takeWhileD takeWhile_nth)

lemma length_dropWhile_eq: "k < length xs \<Longrightarrow> (\<And>n. n < k \<Longrightarrow> P (xs ! n)) \<Longrightarrow> \<not>P (xs ! k) \<Longrightarrow>
                            length (dropWhile P xs) = length xs - k"
  by (simp add: dropWhile_eq_drop length_takeWhile_eq)

lemma take_length_takeWhile: "x \<in> set (take (length (takeWhile P xs)) xs) \<Longrightarrow> P x"
  by (metis set_takeWhileD takeWhile_eq_take)

lemma hd_drop_length_takeWhile: "drop (length (takeWhile P xs)) xs = h#t \<Longrightarrow> P h \<Longrightarrow> False"
  by (metis drop_all hd_drop_conv_nth linorder_not_less list.distinct(1) list.sel(1) nth_length_takeWhile)

lemma prefix_replicate_iff [iff]: "prefix (replicate n x) (replicate m x) \<longleftrightarrow> n \<le> m"
proof
  assume a1: "prefix (x \<up> n) (x \<up> m)"
  show "n \<le> m" using a1 prefix_length_le by fastforce
next
  assume "n \<le> m"
  hence [symmetric]: "(x \<up> n) @ (x \<up> (m - n)) = (x \<up> m)"
    by (metis add_diff_inverse_nat linorder_not_less replicate_add)
  thus "prefix (x \<up> n) (x \<up> m)" by (rule prefixI)
qed

lemma suffix_repl_iff_prefix: "suffix (replicate n x) (replicate m x) \<longleftrightarrow>
                               prefix (replicate n x) (replicate m x)"
  by (simp add: suffix_to_prefix)

lemmas suffix_replicate_iff [iff] = prefix_replicate_iff [folded suffix_repl_iff_prefix]

lemma set_takeWhile_subset: "set (takeWhile P xs) \<subseteq> set xs"
proof
  fix x :: 'a
  assume a1: "x \<in> set (takeWhile P xs)"
  have 1: "x \<in> set (take (length (takeWhile P xs)) xs)"
    using a1 by (subst (asm) takeWhile_eq_take)
  show "x \<in> set xs" using 1 by (rule in_set_takeD)
qed

lemma set_dropWhile_subset: "set (dropWhile P xs) \<subseteq> set xs"
proof
  fix x :: 'a
  assume a1: "x \<in> set (dropWhile P xs)"
  have 1: "x \<in> set (drop (length (takeWhile P xs)) xs)"
    using a1 by (subst (asm) dropWhile_eq_drop)
  show "x \<in> set xs" using 1 by (rule in_set_dropD)
qed

lemma in_set_take_iff: "x \<in> set (take n xs) \<longleftrightarrow> (\<exists>k. k < length xs \<and> k < n \<and> xs ! k = x)"
  apply auto
   apply (metis length_take min_less_iff_conj nth_take set_listE)
  using in_set_conv_nth by fastforce

lemma in_set_drop_iff: "x \<in> set (drop n xs) \<longleftrightarrow> (\<exists>k. k \<ge> n \<and> k < length xs \<and> xs ! k = x)"
proof (induction n arbitrary: xs)
  case 0
  then show ?case apply auto
    by (metis set_listE)
next
  case (Suc n)
  have 1: "drop (Suc n) xs = drop n (tl xs)" by (rule drop_Suc)
  show ?case unfolding 1 Suc apply auto
     apply (metis One_nat_def Suc_lessI diff_Suc_Suc length_tl less_Suc_eq_le less_imp_diff_less
        linorder_not_le nth_tl)
  proof -
    fix k :: nat
    assume a1: "Suc n \<le> k" and a2: "k < length xs"
    show "\<exists>k'\<ge>n. k' < length xs - Suc 0 \<and> tl xs ! k' = xs ! k"
      apply (rule exI [where x="k - 1"])
      apply auto
      using a1 apply simp
      using a1 a2 apply simp
      by (metis a1 a2 diff_Suc_Suc diff_Suc_1' linorder_not_le diff_0_eq_0 list.size(3)
          less_Suc_eq_le Suc_less_eq Suc_pred nth_Cons_Suc neq0_conv list.exhaust_sel)
  qed
qed

lemma set_singleton_iff: "xs \<noteq> [] \<Longrightarrow> set xs = {a} \<longleftrightarrow> (\<forall>i<length xs. xs ! i = a)"
  apply safe
    apply simp_all
    apply fastforce
   apply (metis in_set_conv_nth)
  by fastforce

lemma filter_eq_iff_in_set_eq: "filter P xs = filter Q xs \<longleftrightarrow> (\<forall>x\<in>set xs. P x \<longleftrightarrow> Q x)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case apply auto
    using local.Cons apply blast
    using local.Cons apply fastforce
    using local.Cons apply blast
        apply (metis filter_eq_Cons_iff)
       apply (metis filter_eq_Cons_iff)
    using local.Cons apply blast
    using local.Cons apply fastforce
    using local.Cons by blast
qed

lemma filter_eq_iff_nth_eq: "filter P xs = filter Q xs \<longleftrightarrow> (\<forall>i<length xs. P (xs ! i) \<longleftrightarrow> Q (xs ! i))"
  unfolding filter_eq_iff_in_set_eq by (rule all_set_conv_all_nth)

lemma length_filter_eqI: "length xs = length ys \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> P (xs ! i) \<longleftrightarrow> Q (ys ! i)) \<Longrightarrow>
                          length (filter P xs) = length (filter Q ys)"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain h :: 'b and t :: "'b list" where ys_ht: "ys = h#t" using Cons(2)
    by (metis Cons.prems(1) length_Cons list.size(3) list.exhaust nat.distinct(1))
  have 1: "length xs = length t" using Cons(2) ys_ht by simp
  have 2: "\<And>i. i < length xs \<Longrightarrow> P (xs ! i) = Q (t ! i)" using Cons(3) unfolding ys_ht by fastforce
  note 3 = Cons(1) [OF 1 2, simplified]
  show ?case unfolding ys_ht filter.simps apply auto
       apply (rule 3)
    using Cons.prems(2) ys_ht apply fastforce
     apply (metis Cons.prems(2) ys_ht nth_Cons_0 length_greater_0_conv list.distinct(1))
    by (rule 3)
qed

lemma length_filter_less_eq: "length (filter (\<lambda>i. i < (k::nat)) [0..<(n::nat)]) = min n k"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case apply auto unfolding Suc by simp
qed


lemma in_set_tlD: "x \<in> set (tl xs) \<Longrightarrow> x \<in> set xs"
  by (cases xs) simp_all

lemma map_f_invf_is_id: "bij_betw f M1 M2 \<Longrightarrow> set xs \<subseteq> M2 \<Longrightarrow> map (f \<circ> inv f) xs = xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case using Cons(2, 3) apply auto
     apply (metis (mono_tags, lifting) bij_betw_inv_into_right f_inv_into_f range_eqI)
    using Cons(1) by simp
qed
end