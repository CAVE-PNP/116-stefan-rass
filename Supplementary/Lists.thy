section\<open>Lists\<close>

theory Lists
  imports Main Misc
    "HOL-Library.More_List"
    "HOL-Library.Sublist"
    "HOL-Eisbach.Eisbach"
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


\<comment> \<open>From \<^session>\<open>Universal_Turing_Machine\<close>.\<close>
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
    also from ge have "... = ?lxs div ?n + 1" by (subst div_geq[symmetric]) auto
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
    also from ge have "... = ?lxs div ?n" by (subst div_geq[symmetric]) auto
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

end
