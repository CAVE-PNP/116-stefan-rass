theory Lists3
  imports "Supplementary/Misc" Cook_Levin.Lists_Lists
begin


section \<open>Lists of lists of numbers\label{s:tm-From}\<close>

text \<open>
In this section we introduce a representation for lists of lists of numbers as
symbol sequences over the quaternary alphabet @{text "\<zero>\<one>\<bar>d"} and devise Turing
machines for the few operations on such lists that we need.

A tape containing such representations corresponds to a variable of type @{typ
"'a list"}. A tape in the start configuration corresponds to the empty
list of lists of numbers.

Many proofs in this section are copied from the previous section with minor
modifications, mostly replacing the symbol @{text "\<bar>"} with @{text d}.
\<close>


subsection \<open>Representation as symbol sequence\label{s:tm-From-repr}\<close>

text \<open>
We apply the same principle as for representing lists of numbers. To represent a
list of lists of numbers, every element, which is now a list of numbers, is
terminated by the symbol @{text d}. In this way the empty symbol sequence
represents the empty list of lists of numbers.  The list $[[]]$ containing only
an empty list is represented by @{text d} and the list $[[0]]$ containing only a
list containing only a~0 is represented by @{text "\<bar>d"}. As another example, the
list $[[14,0,0,7],[],[0],[25]]$ is represented by @{text
"\<zero>\<one>\<one>\<one>\<bar>\<bar>\<bar>\<one>\<one>\<one>\<bar>dd\<bar>d\<one>\<zero>\<zero>\<one>\<one>\<bar>d"}. The number of @{text d} symbols equals
the number of elements in the list.

\null
\<close>


abbreviation "flatmap f xs \<equiv> concat (map f xs)"
  \<comment> \<open>see also \<^const>\<open>List.maps\<close>\<close>


locale mlist =
  fixes d :: symbol \<comment> \<open>delimiter\<close>
    and enc_a :: "'a \<Rightarrow> symbol list" (* TODO rename *)
  assumes proper_delim: "d > 1"
    and proper_symbols_e: "\<And>a. proper_symbols (enc_a a)"
    and symbols_lt_e: "\<And>a. symbols_lt d (enc_a a)"
    and e_inj: "\<And>a b. enc_a a = enc_a b \<Longrightarrow> a = b"
begin


abbreviation "len_a a \<equiv> length (enc_a a)"


lemma proper_delim': "proper_symbols [d]" using proper_delim by simp

(* abbreviation (input) sslash_symbol :: nat ("\<sslash>")  where "\<sslash> \<equiv> 5" *)

(* abbreviation "enc_a2 \<equiv> From" *)

definition From :: "'a list \<Rightarrow> symbol list" where
  "From as \<equiv> flatmap (\<lambda>a. enc_a a @ [d]) as"

lemma From_Nil[simp]: "From [] = []"
  unfolding From_def by simp

lemma From_singleton[simp]: "From [a] = enc_a a @ [d]"
  unfolding From_def by simp

(* proposition "From [[]] = [d]" *)
  (* unfolding enc_a3_def by (simp add: From_Nil) *)

lemma proper_symbols_From: "proper_symbols (From as)"
proof (induction as)
  case Nil
  then show ?case
    using From_def by simp
next
  case (Cons a as)
  have "From (a # as) = enc_a a @ [d] @ From as"
    unfolding From_def by simp
  with proper_symbols_e proper_delim' show ?case
    using proper_symbols_append Cons by presburger
qed

lemma symbols_lt_append:
  fixes xs ys :: "symbol list" and z :: symbol
  assumes "symbols_lt z xs" and "symbols_lt z ys"
  shows "symbols_lt z (xs @ ys)"
  using assms prop_list_append by (simp add: nth_append)

lemma symbols_lt_mono[elim]:
  "symbols_lt n xs \<Longrightarrow> n \<le> m \<Longrightarrow> symbols_lt m xs" by fastforce

lemma list_all_length_conv[iff?]: "(\<forall>i<length xs. P (xs ! i)) \<longleftrightarrow> (\<forall>x\<in>set xs. P x)"
  by (fold list_all_length list_all_iff) simp

lemma symbols_lt_altdef: "symbols_lt n xs \<longleftrightarrow> (\<forall>x\<in>set xs. x < n)"
  by (fact list_all_length_conv)

lemma symbols_lt_altdef2: "symbols_lt n xs \<longleftrightarrow> set xs \<subseteq> {..<n}"
  unfolding symbols_lt_altdef by blast

lemma symbols_lt_From:
  assumes "H > d"
  shows "symbols_lt H (From as)"
proof (induction as)
  case Nil
  then show ?case
    using From_def by simp
next
  case (Cons a as)
  have "From (a # as) = enc_a a @ [d] @ From as"
    unfolding From_def by simp
  moreover have "symbols_lt H (enc_a a)"
    using assms symbols_lt_e unfolding symbols_lt_altdef by fastforce
  moreover have "symbols_lt H [d]"
    using assms by simp
  ultimately show ?case
    using symbols_lt_append[of _ H] Cons by presburger
qed


lemma append_Cons_eq_iff2: \<comment> \<open>Similar to @{thm append_Cons_eq_iff}, the proof of which also works on this one for some reason.\<close>
  assumes "x \<notin> set xs" and "x \<notin> set xs'"
  shows "(xs @ x # ys = xs' @ x # ys') = (xs = xs' \<and> ys = ys')"
  using assms by (auto simp: append_eq_Cons_conv Cons_eq_append_conv append_eq_append_conv2)

lemma symbols_lt_prefix_eq:
  assumes "(x @ [d]) @ xs = (y @ [d]) @ ys" and "symbols_lt d x" and "symbols_lt d y"
  shows "x = y"
proof -
  from assms(1) have "x @ d # xs = y @ d # ys" by simp
  with assms(2-3) show "x = y" unfolding symbols_lt_altdef
    by (subst (asm) append_Cons_eq_iff2) blast+
qed

lemma From_inj: "From ns1 = From ns2 \<Longrightarrow> ns1 = ns2"
proof (induction ns1 arbitrary: ns2)
  case Nil
  then show ?case
    using From_def by simp
next
  case (Cons n ns1)
  have 1: "From (n # ns1) = (enc_a n @ [d]) @ From ns1"
    using From_def by simp
  then have "From ns2 = (enc_a n @ [d]) @ From ns1"
    using Cons by simp
  then have "ns2 \<noteq> []"
    using From_Nil by auto
  then have 2: "ns2 = hd ns2 # tl ns2"
    using `ns2 \<noteq> []` by simp
  then have 3: "From ns2 = (enc_a (hd ns2) @ [d]) @ From (tl ns2)"
    using From_def by (metis concat.simps(2) list.simps(9))

  have 4: "hd ns2 = n"
    using symbols_lt_prefix_eq 1 3 symbols_lt_e e_inj Cons by metis
  then have "From ns2 = (enc_a n @ [d]) @ From (tl ns2)"
    using 3 by simp
  then have "From ns1 = From (tl ns2)"
    using 1 by (simp add: Cons.prems)
  then have "ns1 = tl ns2"
    using Cons by simp
  then show ?case
    using 2 4 by simp
qed

lemma From_append: "From (xs @ ys) = From xs @ From ys"
  using From_def by simp

text \<open>
Similar to @{text "\<lfloor>_\<rfloor>\<^sub>N"} and @{text "\<lfloor>_\<rfloor>\<^sub>N\<^sub>L"}, the tape contents for a list
of list of numbers:
\<close>

definition xcontents :: "'a \<Rightarrow> (nat \<Rightarrow> symbol)" ("\<lfloor>_\<rfloor>\<^sub>X") where
  "\<lfloor>a\<rfloor>\<^sub>X \<equiv> \<lfloor>enc_a a\<rfloor>"

definition lxcontents :: "'a list \<Rightarrow> (nat \<Rightarrow> symbol)" ("\<lfloor>_\<rfloor>\<^sub>L\<^sub>X") where
  "\<lfloor>as\<rfloor>\<^sub>L\<^sub>X \<equiv> \<lfloor>From as\<rfloor>"

lemma clean_tape_lxcontents: "clean_tape (\<lfloor>as\<rfloor>\<^sub>L\<^sub>X, i)"
  by (simp add: lxcontents_def proper_symbols_From)

lemma lxcontents_Nil: "\<lfloor>[]\<rfloor>\<^sub>L\<^sub>X = \<lfloor>[]\<rfloor>"
  using lxcontents_def by simp

text \<open>
Similar to @{const nlength} and @{const len_a}, the length of the
representation of a list of lists of numbers:
\<close>

definition lxlength :: "'a list \<Rightarrow> nat" where
  "lxlength as \<equiv> length (From as)"

lemma lxlength: "lxlength as = (\<Sum>a\<leftarrow>as. Suc (len_a a))"
  using lxlength_def From_def by (induction as) simp_all

lemma lxlength_Nil [simp]: "lxlength [] = 0"
  using lxlength_def From_def by simp

lemma lxlength_Cons: "lxlength (a # as) = Suc (len_a a) + lxlength as"
  by (simp add: lxlength)

lemma length_le_lxlength: "length as \<le> lxlength as"
  using lxlength sum_list_mono[of as "\<lambda>_. 1" "\<lambda>a. Suc (len_a a)"] sum_list_const[of 1 as]
  by force

lemma member_le_lxlength_1: "a \<in> set as \<Longrightarrow> len_a a \<le> lxlength as - 1"
  using lxlength by (induction as) auto

lemma lxlength_take:
  assumes "i < length as"
  shows "lxlength (take i as) + len_a (as ! i) < lxlength as"
proof -
  have "as = take i as @ [as ! i] @ drop (Suc i) as"
    using assms by (metis Cons_eq_appendI append_self_conv2 id_take_nth_drop)
  then have "From as = From (take i as) @ From [as ! i] @ From (drop (Suc i) as)"
    using From_append by metis
  then have "lxlength as = lxlength (take i as) + lxlength [as ! i] + lxlength (drop (Suc i) as)"
    by (simp add: lxlength_def)
  then have "lxlength as \<ge> lxlength (take i as) + lxlength [as ! i]"
    by simp
  then have "lxlength as \<ge> lxlength (take i as) + Suc (len_a (as ! i))"
    using lxlength by simp
  then show ?thesis
    by simp
qed

lemma take_drop_From:
  assumes "i < length as"
  shows "take (Suc (len_a (as ! i))) (drop (lxlength (take i as)) (From as)) = enc_a (as ! i) @ [d]"
proof -
  have "From as = From (take i as) @ From (drop i as)"
    using From_append by (metis append_take_drop_id)
  moreover have "From (drop i as) = From [as ! i] @ From (drop (Suc i) as)"
    using assms From_append by (metis Cons_nth_drop_Suc append_Cons self_append_conv2)
  ultimately have "From as = From (take i as) @ From [as ! i] @ From (drop (Suc i) as)"
    by simp
  then have "drop (lxlength (take i as)) (From as) = From [as ! i] @ From (drop (Suc i) as)"
    by (simp add: lxlength_def)
  then have "drop (lxlength (take i as)) (From as) = enc_a (as ! i) @ [d] @ From (drop (Suc i) as)"
    using From_def by simp
  then show ?thesis by fastforce
qed

corollary take_drop_From':
  assumes "i < length ns"
  shows "take (len_a (ns ! i)) (drop (lxlength (take i ns)) (From ns)) = enc_a (ns ! i)"
  using take_drop_From[OF assms] by (metis append_assoc append_eq_conv_conj append_take_drop_id)

corollary From_take_at_term:
  assumes "i < length ns"
  shows "From ns ! (lxlength (take i ns) + len_a (ns ! i)) = d"
  using assms take_drop_From lxlength_def From_append
  by (smt (z3) append_eq_conv_conj append_take_drop_id lessI nth_append_length nth_append_length_plus nth_take)

lemma lxlength_take_Suc:
  assumes "i < length ns"
  shows "lxlength (take i ns) + Suc (len_a (ns ! i)) = lxlength (take (Suc i) ns)"
proof -
  have "ns = take i ns @ [ns ! i] @ drop (Suc i) ns"
    using assms by (metis Cons_eq_appendI append_self_conv2 id_take_nth_drop)
  then have "From ns = From (take i ns) @ From [ns ! i] @ From (drop (Suc i) ns)"
    using From_append by metis
  then have "lxlength ns = lxlength (take i ns) + lxlength [ns ! i] + lxlength (drop (Suc i) ns)"
    by (simp add: lxlength_def)
  moreover have "lxlength ns = lxlength (take (Suc i) ns) + lxlength (drop (Suc i) ns)"
    using From_append by (metis append_take_drop_id length_append lxlength_def)
  ultimately have "lxlength (take (Suc i) ns) = lxlength (take i ns) + lxlength [ns ! i]"
    by simp
  then show ?thesis
    using lxlength by simp
qed

lemma From_take_at:
  assumes "i < length ns" and "j < len_a (ns ! i)"
  shows "From ns ! (lxlength (take i ns) + j) = enc_a (ns ! i) ! j"
proof -
  have "ns = take i ns @ [ns ! i] @ drop (Suc i) ns"
    using assms by (metis Cons_eq_appendI append_self_conv2 id_take_nth_drop)
  then have "From ns = (From (take i ns) @ From [ns ! i]) @ From (drop (Suc i) ns)"
    using From_append by (metis append_assoc)
  moreover have "lxlength (take i ns) + j < lxlength (take i ns) + lxlength [ns ! i]"
    using assms(2) lxlength by simp
  ultimately have "From ns ! (lxlength (take i ns) + j) =
      (From (take i ns) @ From [ns ! i]) ! (lxlength (take i ns) + j)"
    by (metis length_append lxlength_def nth_append)
  also have "... = From [ns ! i] ! j"
    by (simp add: lxlength_def)
  also have "... = (enc_a (ns ! i) @ [d]) ! j"
    using From_def by simp
  also have "... = enc_a (ns ! i) ! j"
    using assms(2) by (metis nth_append)
  finally show ?thesis .
qed

lemma lxcontents_rneigh_5:
  assumes "i < length ns"
  shows "rneigh (\<lfloor>ns\<rfloor>\<^sub>L\<^sub>X, Suc (lxlength (take i ns))) {d} (len_a (ns ! i))"
proof (rule rneighI)
  let ?tp = "(\<lfloor>ns\<rfloor>\<^sub>L\<^sub>X, Suc (lxlength (take i ns)))"
  show "fst ?tp (snd ?tp + len_a (ns ! i)) \<in> {d}"
  proof -
    have "snd ?tp + len_a (ns ! i) \<le> lxlength ns"
      using lxlength_take assms by (simp add: Suc_leI)
    then have "fst ?tp (snd ?tp + len_a (ns ! i)) =
        From ns ! (lxlength (take i ns) + len_a (ns ! i))"
      using lxcontents_def contents_inbounds lxlength_def by simp
    then show ?thesis
      using From_take_at_term assms by simp
  qed
  show "fst ?tp (snd ?tp + j) \<notin> {d}" if "j < len_a (ns ! i)" for j
  proof -
    have "snd ?tp + len_a (ns ! i) \<le> lxlength ns"
      using lxlength_take assms by (simp add: Suc_leI)
    then have "snd ?tp + j \<le> lxlength ns"
      using that by simp
    then have "fst ?tp (snd ?tp + j) = From ns ! (lxlength (take i ns) + j)"
      using lxcontents_def contents_inbounds lxlength_def by simp
    then have "fst ?tp (snd ?tp + j) = enc_a (ns ! i) ! j"
      using assms that From_take_at by simp
    moreover have "enc_a (ns ! i) ! j \<noteq> d"
      using symbols_lt_e that nth_mem by fast
    ultimately show ?thesis
      by simp
  qed
qed

text \<open>
A tape containing a list of lists of numbers, with the tape head after all
the symbols:
\<close>

abbreviation lxtape :: "'a list \<Rightarrow> tape" where
  "lxtape ns \<equiv> (\<lfloor>ns\<rfloor>\<^sub>L\<^sub>X, Suc (lxlength ns))"

text \<open>
Like before but with the tape head or at the beginning of the $i$-th list
element:
\<close>

abbreviation lxtape' :: "'a list \<Rightarrow> nat \<Rightarrow> tape" where
  "lxtape' ns i \<equiv> (\<lfloor>ns\<rfloor>\<^sub>L\<^sub>X, Suc (lxlength (take i ns)))"

lemma lxtape'_0: "lxtape' ns 0 = (\<lfloor>ns\<rfloor>\<^sub>L\<^sub>X, 1)"
  using lxlength by simp

lemma lxtape'_tape_read: "|.| (lxtape' as i) = 0 \<longleftrightarrow> i \<ge> length as"
proof -
  have "|.| (lxtape' as i) = 0" if "i \<ge> length as" for i
  proof -
    have "lxtape' as i \<equiv> (\<lfloor>as\<rfloor>\<^sub>L\<^sub>X, Suc (lxlength as))"
      using that by simp
    then show ?thesis
      using lxcontents_def contents_outofbounds lxlength_def
      by (metis Suc_eq_plus1 add.left_neutral fst_conv less_Suc0 less_add_eq_less snd_conv)
  qed
  moreover have "|.| (lxtape' as i) \<noteq> 0" if "i < length as" for i
    using that lxcontents_def contents_inbounds lxlength_def lxlength_take proper_symbols_From
    by (metis Suc_leI add_Suc_right diff_Suc_1 fst_conv less_add_same_cancel1 less_le_trans not_add_less2
      plus_1_eq_Suc snd_conv zero_less_Suc)
  ultimately show ?thesis
    by (meson le_less_linear)
qed


subsection \<open>Appending an element\<close>

text \<open>
The next Turing machine is very similar to @{const tm_append}, just with
terminator symbol @{text d} instead of @{text "\<bar>"}. It appends a list of
numbers given on tape $j_2$ to the list of lists of numbers on tape $j_1$.
\<close>

definition (in -) tm_appendl :: "symbol \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_appendl d j1 j2 \<equiv>
    tm_right_until j1 {\<box>} ;;
    tm_cp_until j2 j1 {\<box>} ;;
    tm_cr j2 ;;
    tm_char j1 d"


method_setup distinct_subgoals =
  \<open>Scan.succeed (K (SIMPLE_METHOD distinct_subgoals_tac))\<close>

named_theorems tm_intro
declare turing_machine_sequential_turing_machine[tm_intro]
  tm_right_until_tm[tm_intro]
  tm_cp_until_tm[tm_intro]
  tm_char_tm[tm_intro]
  tm_cr_tm[tm_intro]

method tm_intro uses add intro =
  intro tm_intro,
  distinct_subgoals;
  (fact add | fact)?

lemma tm_appendl_tm[tm_intro]:
  assumes "0 < j1" and "G > d" and "G \<ge> 4" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_appendl d j1 j2)"
  unfolding tm_appendl_def by (tm_intro) (use assms in force)

end \<comment> \<open>\<^locale>\<open>mlist\<close>\<close>

locale turing_machine_appendl = mlist +
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_right_until j1 {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_cp_until j2 j1 {\<box>}"
definition "tm3 \<equiv> tm2 ;; tm_cr j2"
definition "tm4 \<equiv> tm3 ;; tm_char j1 d"

lemma tm4_eq_tm_append: "tm4 = tm_appendl d j1 j2"
  unfolding tm4_def tm3_def tm2_def tm1_def tm_appendl_def by simp

context
  fixes tps0 :: "tape list" and k i1 :: nat and a :: 'a and as :: "'a list"
  assumes jk: "length tps0 = k" "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j1"
    and i1: "i1 \<le> Suc (lxlength as)"
  assumes tps0:
     "tps0 ! j1 = (\<lfloor>as\<rfloor>\<^sub>L\<^sub>X, i1)"
     "tps0 ! j2 = (\<lfloor>enc_a a\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0[j1 := lxtape as]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (Suc (lxlength as) - i1)"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: jk)
  let ?l = "Suc (lxlength as) - i1"
  show "rneigh (tps0 ! j1) {0} ?l"
  proof (rule rneighI)
    show "(tps0 ::: j1) (tps0 :#: j1 + ?l) \<in> {0}"
      using tps0 jk lxcontents_def lxlength_def by simp
    show "(tps0 ::: j1) (tps0 :#: j1 + i) \<notin> {0}" if "i < Suc (lxlength as) - i1" for i
    proof -
      have "i1 + i < Suc (lxlength as)"
        using that i1 by simp
      then show ?thesis
        using proper_symbols_From lxlength_def tps0 lxcontents_def contents_def
        by (metis One_nat_def Suc_leI diff_Suc_1 fst_conv less_Suc_eq_0_disj less_nat_zero_code singletonD snd_conv)
    qed
  qed
  show "ttt = Suc (Suc (lxlength as) - i1)"
    using assms(1) .
  show "tps1 = tps0[j1 := tps0 ! j1 |+| Suc (lxlength as) - i1]"
    using tps1_def tps0 i1 by simp
qed

definition "tps2 \<equiv> tps0
  [j1 := (\<lfloor>From as @ enc_a a\<rfloor>, Suc (lxlength as) + len_a a),
   j2 := (\<lfloor>enc_a a\<rfloor>, Suc (len_a a))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 3 + lxlength as - i1 + len_a a"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: jk tps1_def)
  have j1: "tps1 ! j1 = lxtape as"
    using tps1_def by (simp add: jk)
  have j2: "tps1 ! j2 = (\<lfloor>enc_a a\<rfloor>, 1)"
    using tps1_def tps0 jk by simp
  show "rneigh (tps1 ! j2) {0} (len_a a)"
  proof (rule rneighI)
    show "(tps1 ::: j2) (tps1 :#: j2 + len_a a) \<in> {0}"
      using j2 by (simp add: nlcontents_def)
    show "\<And>i. i < len_a a \<Longrightarrow> (tps1 ::: j2) (tps1 :#: j2 + i) \<notin> {0}"
      using j2 tps0 contents_def nlcontents_def proper_symbols_e by fastforce
  qed
  show "tps2 = tps1
    [j2 := tps1 ! j2 |+| len_a a,
     j1 := implant (tps1 ! j2) (tps1 ! j1) (len_a a)]"
    (is "_ = ?rhs")
  proof -
    have "implant (tps1 ! j2) (tps1 ! j1) (len_a a) = implant (\<lfloor>enc_a a\<rfloor>, 1) (lxtape as) (len_a a)"
      using j1 j2 by simp
    also have "... =
      (\<lfloor>From as @ (take (len_a a) (drop (1 - 1) (enc_a a)))\<rfloor>,
       Suc (length (From as)) + len_a a)"
      using implant_contents nlcontents_def lxcontents_def lxlength_def by simp
    also have "... = (\<lfloor>From as @ enc_a a\<rfloor>, Suc (length (From as)) + len_a a)"
      by simp
    also have "... = (\<lfloor>From as @ enc_a a\<rfloor>, Suc (lxlength as) + len_a a)"
      using lxlength_def by simp
    also have "... = tps2 ! j1"
      using jk tps2_def by (metis nth_list_update_eq nth_list_update_neq)
    finally have "implant (tps1 ! j2) (tps1 ! j1) (len_a a) = tps2 ! j1" .
    then have "tps2 ! j1 = implant (tps1 ! j2) (tps1 ! j1) (len_a a)"
      by simp
    then have "tps2 ! j1 = ?rhs ! j1"
      using tps1_def jk by (metis length_list_update nth_list_update_eq)
    moreover have "tps2 ! j2 = ?rhs ! j2"
      using tps2_def tps1_def jk j2 by simp
    moreover have "tps2 ! j = ?rhs ! j" if "j < length tps2" "j \<noteq> j1" "j \<noteq> j2" for j
      using that tps2_def tps1_def by simp
    moreover have "length tps2 = length ?rhs"
      using tps1_def tps2_def by simp
    ultimately show ?thesis
      using nth_equalityI by blast
  qed
  show "ttt = Suc (Suc (lxlength as) - i1) + Suc (len_a a)"
    using assms(1) j1 tps0 i1 by simp
qed

definition "tps3 \<equiv> tps0
  [j1 := (\<lfloor>From as @ enc_a a\<rfloor>, Suc (lxlength as) + len_a a)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 6 + lxlength as - i1 + 2 * len_a a"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: jk i1 tps2_def)
  let ?tp1 = "(\<lfloor>From as @ enc_a a\<rfloor>, Suc (lxlength as + len_a a))"
  let ?tp2 = "(\<lfloor>enc_a a\<rfloor>, Suc (len_a a))"
  show "clean_tape (tps2 ! j2)"
     by (force simp: proper_symbols_e tps2_def jk)
  show "tps3 = tps2[j2 := tps2 ! j2 |#=| 1]"
    using tps3_def tps2_def jk tps0(2)
    by (metis fst_eqD length_list_update list_update_overwrite list_update_same_conv nth_list_update)
  show "ttt = 3 + lxlength as - i1 + len_a a + (tps2 :#: j2 + 2)"
    using assms tps2_def jk tps0 i1 by simp
qed

definition "tps4 \<equiv> tps0
  [j1 := (\<lfloor>From (as @ [a])\<rfloor>, Suc (lxlength (as @ [a])))]"

lemma tm4:
  assumes "ttt = 7 + lxlength as - i1 + 2 * len_a a"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: jk tps3_def time: jk i1 assms)
  show "tps4 = tps3[j1 := tps3 ! j1 |:=| d |+| 1]"
    (is "tps4 = ?tps")
  proof -
    have "tps3 ! j1 = (\<lfloor>From as @ enc_a a\<rfloor>, Suc (lxlength as) + len_a a)"
      using tps3_def jk by simp
    then have "?tps = tps0[j1 := (\<lfloor>From as @ enc_a a\<rfloor>, Suc (lxlength as + len_a a)) |:=| d |+| 1]"
      using tps3_def by simp
    moreover have "(\<lfloor>From as @ enc_a a\<rfloor>, Suc (lxlength as + len_a a)) |:=| d |+| 1 =
        (\<lfloor>From (as @ [a])\<rfloor>, Suc (lxlength (as @ [a])))"
      (is "?lhs = ?rhs")
    proof -
      have "?lhs =
        (\<lfloor>From as @ enc_a a\<rfloor>(Suc (lxlength as + len_a a) := d),
         Suc (Suc (lxlength as + len_a a)))"
        by simp
      also have "... =
        (\<lfloor>From as @ enc_a a\<rfloor>(Suc (lxlength as + len_a a) := d),
         Suc (lxlength (as @ [a])))"
        using lxlength_def From_def by simp
      also have "... = (\<lfloor>(From as @ enc_a a) @ [d]\<rfloor>, Suc (lxlength (as @ [a])))"
        using contents_snoc lxlength_def by (metis length_append)
      also have "... = (\<lfloor>From as @ enc_a a @ [d]\<rfloor>, Suc (lxlength (as @ [a])))"
        by simp
      also have "... = (\<lfloor>From (as @ [a])\<rfloor>, Suc (lxlength (as @ [a])))"
        using From_def by simp
      finally show "?lhs = ?rhs" .
    qed
    ultimately show ?thesis
      using tps4_def by auto
  qed
qed

end  (* context *)

end  (* locale turing_machine_appendl *)

lemma (in mlist) transforms_tm_appendlI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and ttt k i1 :: nat and a :: 'a and as :: "'a list"
  assumes "length tps = k" "j1 < k" "j2 < k" "j1 \<noteq> j2"
  assumes "0 < j1"
  assumes "i1 \<le> Suc (mlist.lxlength d enc_a as)"
  assumes
    "tps ! j1 = (mlist.lxcontents d enc_a as, i1)"
    "tps ! j2 = (\<lfloor>enc_a a\<rfloor>, 1)"
  assumes "ttt = 7 + mlist.lxlength d enc_a as - i1 + 2 * length (enc_a a)"
  assumes tps': "tps' = tps
    [j1 := mlist.lxtape d enc_a (as @ [a])]"
  shows "transforms (tm_appendl d j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_appendl d enc_a j1 j2 by unfold_locales
  have tps4: "tps' = loc.tps4 tps a as" unfolding tps' lxcontents_def
    unfolding loc.tps4_def[OF assms(1-8)] ..
  show ?thesis unfolding loc.tm4_eq_tm_append[symmetric] tps4
    using assms(1-9) by (fact loc.tm4)
qed


subsection \<open>Extending with a list\<close>

text \<open>
The next Turing machine extends a list of lists of numbers with another list of
lists of numbers. It is in fact the same TM as for extending a list of numbers
because in both cases extending means simply copying the contents from one tape
to another.  We introduce a new name for this TM and express the semantics in
terms of lists of lists of numbers.  The proof is almost the same except with
@{const mlist.len_a} replaced by @{const mlist.lxlength} and so on.
\<close>

definition tm_extendl :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_extendl \<equiv> tm_extend"

lemma tm_extendl_tm:
  assumes "0 < j1" and "G \<ge> 4" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_extendl j1 j2)"
  unfolding tm_extendl_def using assms tm_extend_tm by simp

locale turing_machine_extendl = mlist +
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_cp_until j2 j1 {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_cr j2"

lemma tm2_eq_tm_extendl: "tm2 = tm_extendl j1 j2"
  unfolding tm2_def tm2_def tm1_def tm_extendl_def tm_extend_def by simp

context
  fixes tps0 :: "tape list" and k :: nat and as1 as2 :: "'a list"
  assumes jk: "0 < j1" "j1 < k" "j2 < k" "j1 \<noteq> j2" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = lxtape as1"
    "tps0 ! j2 = (\<lfloor>as2\<rfloor>\<^sub>L\<^sub>X, 1)"
begin

definition "tps1 \<equiv> tps0
  [j1 := mlist.lxtape d enc_a (as1 @ as2),
   j2 := mlist.lxtape d enc_a as2]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (lxlength as2)"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps1_def tps0 jk time: assms)
  let ?n = "lxlength as2"
  show "rneigh (tps0 ! j2) {\<box>} ?n"
  proof (rule rneighI)
    show "(tps0 ::: j2) (tps0 :#: j2 + lxlength as2) \<in> {\<box>}"
      using tps0 mlist.lxcontents_def mlist.lxlength_def jk
      by (metis contents_outofbounds fst_eqD lessI mlist_axioms plus_1_eq_Suc singleton_iff snd_eqD)
    show "\<And>i. i < lxlength as2 \<Longrightarrow> (tps0 ::: j2) (tps0 :#: j2 + i) \<notin> {\<box>}"
      using tps0 jk contents_def lxcontents_def lxlength_def proper_symbols_From
      by fastforce
  qed
  show "tps1 = tps0
    [j2 := tps0 ! j2 |+| lxlength as2,
     j1 := implant (tps0 ! j2) (tps0 ! j1) (lxlength as2)]"
  proof -
    have "implant (\<lfloor>as2\<rfloor>\<^sub>L\<^sub>X, 1) (lxtape as1) (lxlength as2) = lxtape (as1 @ as2)"
      using lxcontents_def lxlength_def implant_contents by (simp add: From_append)
    moreover have "tps1 ! j2 = tps0 ! j2 |+| lxlength as2"
      using tps0 jk tps1_def by simp
    ultimately show ?thesis
      using tps0 jk tps1_def by (metis fst_conv list_update_swap plus_1_eq_Suc snd_conv)
  qed
qed

definition "tps2 \<equiv> tps0[j1 := lxtape (as1 @ as2)]"

lemma tm2:
  assumes "ttt = 4 + 2 * lxlength as2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps1_def tps2_def jk time: assms tps1_def jk)
  show "clean_tape (tps1 ! j2)"
    using tps1_def jk clean_tape_lxcontents by simp
  show "tps2 = tps1[j2 := tps1 ! j2 |#=| 1]"
    using tps1_def jk tps2_def tps0(2)
    by (metis fst_conv length_list_update list_update_id list_update_overwrite nth_list_update)
qed

end  (* context tps0 *)

end  (* locale turing_machine_extendl *)

lemma (in mlist) transforms_tm_extendlI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k :: nat and as1 as2 :: "'a list"
  assumes "0 < j1" "j1 < k" "j2 < k" "j1 \<noteq> j2" "length tps = k"
  assumes
    "tps ! j1 = mlist.lxtape d enc_a as1"
    "tps ! j2 = (mlist.lxcontents d enc_a as2, 1)"
  assumes ttt: "ttt = 4 + 2 * mlist.lxlength d enc_a as2"
  assumes tps': "tps' = tps[j1 := mlist.lxtape d enc_a (as1 @ as2)]"
  shows "transforms (tm_extendl j1 j2) tps ttt tps'"
proof -
  note l1 = assms(1-7)
  interpret loc: turing_machine_extendl d enc_a j1 j2 by unfold_locales
  show ?thesis unfolding tps'
    by (fold loc.tm2_eq_tm_extendl loc.tps2_def[OF assms(1-7)]) (fact loc.tm2[OF assms(1-8)])
qed

text \<open>
The next Turing machine erases the appended list.
\<close>

definition tm_extendl_erase :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_extendl_erase j1 j2 \<equiv> tm_extendl j1 j2 ;; tm_erase_cr j2"

lemma tm_extendl_erase_tm:
  assumes "0 < j1" and "0 < j2" and "G \<ge> 4" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_extendl_erase j1 j2)"
  unfolding tm_extendl_erase_def using assms tm_extendl_tm tm_erase_cr_tm by simp

lemma (in mlist) transforms_tm_extendl_eraseI [transforms_intros]:
  fixes tps tps' :: "tape list" and j1 j2 :: tapeidx and ttt k :: nat and as1 as2 :: "'a list"
  assumes "0 < j1" "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j2" "length tps = k"
  assumes
    "tps ! j1 = mlist.lxtape d enc_a as1"
    "tps ! j2 = (mlist.lxcontents d enc_a as2, 1)"
  assumes "ttt = 11 + 4 * mlist.lxlength d enc_a as2 "
  assumes "tps' = tps
    [j1 := mlist.lxtape d enc_a (as1 @ as2),
     j2 := (\<lfloor>[]\<rfloor>, 1)]"
  shows "transforms (tm_extendl_erase j1 j2) tps ttt tps'"
  unfolding tm_extendl_erase_def
proof (tform tps: assms)
  let ?zs = "mlist.From d enc_a as2"
  show "tps[j1 := mlist.lxtape d enc_a (as1 @ as2)] ::: j2 = \<lfloor>?zs\<rfloor>"
    using assms by (simp add: lxcontents_def)
  show "proper_symbols ?zs"
    using proper_symbols_From by simp
  show "ttt = 4 + 2 * mlist.lxlength d enc_a as2 +
      (tps[j1 := mlist.lxtape d enc_a (as1 @ as2)] :#: j2 + 2 * length (mlist.From d enc_a as2) + 6)"
    using assms lxlength_def by simp
qed


subsection \<open>Moving to the next element\<close>

text \<open>
Iterating over a list of lists of numbers works with the same Turing machine,
@{const tm_nextract}, as for lists of numbers. We just have to set the parameter
$z$ to the terminator symbol @{text d}.  For the proof
we can also just copy from the previous section, replacing the symbol @{text "\<bar>"}
by @{text d} and @{const mlist.len_a} by @{const mlist.lxlength}, etc.

\null
\<close>

locale turing_machine_nextract_5 =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_erase_cr j2"
definition "tm2 \<equiv> tm1 ;; tm_cp_until j1 j2 {d}"
definition "tm3 \<equiv> tm2 ;; tm_cr j2"
definition "tm4 \<equiv> tm3 ;; tm_right j1"

lemma tm4_eq_tm_nextract: "tm4 = tm_nextract d j1 j2"
  unfolding tm1_def tm2_def tm3_def tm4_def tm_nextract_def by simp

context
  fixes tps0 :: "tape list" and k idx :: nat and as :: "'a list" and dummy :: "nat list"
  assumes jk: "j1 < k" "j2 < k" "0 < j1" "0 < j2" "j1 \<noteq> j2" "length tps0 = k"
    and idx: "idx < length as"
    and tps0:
      "tps0 ! j1 = lxtape' as idx"
      "tps0 ! j2 = (\<lfloor>dummy\<rfloor>\<^sub>N\<^sub>L, 1)"
begin

definition "tps1 \<equiv> tps0[j2 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 7 + 2 * len_a dummy"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: jk idx tps0 tps1_def assms)
  show "proper_symbols (enc_a dummy)"
    using proper_symbols_enc_a by simp
  show "tps1 = tps0[j2 := (\<lfloor>[]\<rfloor>, 1)]"
    using tps1_def by (simp add: nlcontents_def enc_a_Nil)
  show "tps0 ::: j2 = \<lfloor>enc_a dummy\<rfloor>"
    using tps0 by (simp add: nlcontents_def)
  show "ttt = tps0 :#: j2 + 2 * length (enc_a dummy) + 6"
    using tps0 assms by simp
qed

definition "tps2 \<equiv> tps0
  [j1 := (\<lfloor>as\<rfloor>\<^sub>L\<^sub>X, lxlength (take (Suc idx) as)),
   j2 := (\<lfloor>as ! idx\<rfloor>\<^sub>N\<^sub>L, Suc (len_a (as ! idx)))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 7 + 2 * len_a dummy + Suc (len_a (as ! idx))"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: jk idx tps0 tps2_def tps1_def time: assms)
  show "rneigh (tps1 ! j1) {d} (len_a (as ! idx))"
    using tps1_def tps0 jk by (simp add: idx lxcontents_rneigh_5)
  show "tps2 = tps1
    [j1 := tps1 ! j1 |+| len_a (as ! idx),
     j2 := implant (tps1 ! j1) (tps1 ! j2) (len_a (as ! idx))]"
     (is "?l = ?r")
  proof (rule nth_equalityI)
    show len: "length ?l = length ?r"
      using tps1_def tps2_def jk by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      consider "i = j1" | "i = j2" | "i \<noteq> j1 \<and> i \<noteq> j2"
        by auto
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          using tps0 that tps1_def tps2_def jk lxlength_take_Suc[OF idx] idx by simp
      next
        case 2
        then have lhs: "?l ! i = (\<lfloor>as ! idx\<rfloor>\<^sub>N\<^sub>L, Suc (len_a (as ! idx)))"
          using tps2_def jk by simp
        let ?i = "Suc (lxlength (take idx as))"
        have i1: "?i > 0"
          by simp
        have "len_a (as ! idx) + (?i - 1) \<le> lxlength as"
          using idx lxlength_take by (metis add.commute diff_Suc_1 less_or_eq_imp_le)
        then have i2: "len_a (as ! idx) + (?i - 1) \<le> length (From as)"
          using lxlength_def by simp
        have "?r ! i = implant (tps1 ! j1) (tps1 ! j2) (len_a (as ! idx))"
          using 2 tps1_def jk by simp
        also have "... = implant (\<lfloor>as\<rfloor>\<^sub>L\<^sub>X, ?i) (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1) (len_a (as ! idx))"
          using tps1_def jk tps0 by simp
        also have "... =
          (\<lfloor>[] @ (take (len_a (as ! idx)) (drop (?i - 1) (From as)))\<rfloor>,
           Suc (length []) + len_a (as ! idx))"
          using implant_contents[OF i1 i2] lxcontents_def nlcontents_def enc_a_Nil by (metis One_nat_def list.size(3))
        finally have "?r ! i =
          (\<lfloor>[] @ (take (len_a (as ! idx)) (drop (?i - 1) (From as)))\<rfloor>,
           Suc (length []) + len_a (as ! idx))" .
        then have "?r ! i =
          (\<lfloor>take (len_a (as ! idx)) (drop (lxlength (take idx as)) (From as))\<rfloor>,
           Suc (len_a (as ! idx)))"
          by simp
        then have "?r ! i = (\<lfloor>enc_a (as ! idx)\<rfloor>, Suc (len_a (as ! idx)))"
          using take_drop_From'[OF idx] by simp
        then show ?thesis
          using lhs nlcontents_def by simp
      next
        case 3
        then show ?thesis
          using that tps1_def tps2_def jk by simp
      qed
    qed
  qed
qed

definition "tps3 \<equiv> tps0
  [j1 := (\<lfloor>as\<rfloor>\<^sub>L\<^sub>X, lxlength (take (Suc idx) as)),
   j2 := (\<lfloor>as ! idx\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 11 + 2 * len_a dummy + 2 * (len_a (as ! idx))"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: jk idx tps0 tps2_def tps3_def assms)
  show "clean_tape (tps2 ! j2)"
    using tps2_def jk clean_tape_nlcontents by simp
qed

definition "tps4 \<equiv> tps0
  [j1 := lxtape' as (Suc idx),
   j2 := (\<lfloor>as ! idx\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm4:
  assumes "ttt = 12 + 2 * len_a dummy + 2 * (len_a (as ! idx))"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def by (tform tps: jk idx tps0 tps3_def tps4_def assms)

end  (* context *)

end  (* locale turing_machine_nextract *)

lemma transforms_tm_nextract_5I [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k idx :: nat and as :: "'a list" and dummy :: "nat list"
  assumes "j1 < k" "j2 < k" "0 < j1" "0 < j2" "j1 \<noteq> j2" "length tps = k"
    and "idx < length as"
  assumes
    "tps ! j1 = lxtape' as idx"
    "tps ! j2 = (\<lfloor>dummy\<rfloor>\<^sub>N\<^sub>L, 1)"
  assumes "ttt = 12 + 2 * len_a dummy + 2 * (len_a (as ! idx))"
  assumes "tps' = tps
    [j1 := lxtape' as (Suc idx),
     j2 := (\<lfloor>as ! idx\<rfloor>\<^sub>N\<^sub>L, 1)]"
  shows "transforms (tm_nextract d j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_nextract_5 j1 j2 .
  show ?thesis
    using assms loc.tm4 loc.tps4_def loc.tm4_eq_tm_nextract by simp
qed



end
