theory SpaceComplexity
  imports Main Computability
begin
(* TODO: discuss good/proper names for the following definitions! *)

definition output_length :: "(('s::finite) list \<Rightarrow> 's list) \<Rightarrow> nat \<Rightarrow> nat" where
  "output_length f n \<equiv> Max {n'. \<exists>w. length w = n \<and> length (f w) = n'}"

lemma output_lengths_finite: "finite {n'. \<exists>w. length w = n \<and>
                              length ((f::('s::finite) list \<Rightarrow> 's list) w) = n'}"
proof -
  have 1: "{n'. \<exists>w. length w = n \<and> length (f w) = n'} = image (length \<circ> f) {w. length w = n}"
    by auto
  show "finite {n'. \<exists>w. length w = n \<and> length (f w) = n'}" unfolding 1 apply auto
    using finite_list_length by blast
qed

lemma output_lengths_not_empty: "{n'. \<exists>w. length w = n \<and> length (f w) = n'} \<noteq> {}"
  by (simp add: Ex_list_of_length)

lemma output_length_ge: "output_length (f::('s::finite) list \<Rightarrow> 's list) (length w) \<ge>
                         length (f w)"
  unfolding output_length_def
proof -
  have "length (f w) \<in> {n'. \<exists>w'. length w' = length w \<and> length (f w') = n'}" by blast
  thus "length (f w) \<le> Max {n'. \<exists>w'. length w' = length w \<and> length (f w') = n'}"
    using output_lengths_finite Max.coboundedI by blast
qed

lemma output_length_w: obtains w :: "('s::finite) list" where
  "length (f w) = output_length f (length w)"
  unfolding output_length_def using output_lengths_finite [where f=f]
    output_lengths_not_empty [where f=f]
proof -
  assume a1: "\<And>w. length (f w) = Max {n'. \<exists>wa. length wa = length w \<and>
              length (f wa) = n'} \<Longrightarrow> thesis"
  obtain bb :: "nat \<Rightarrow> ('s list \<Rightarrow> 's list) \<Rightarrow> nat \<Rightarrow> bool" where
    f2: "\<forall>X0 X1 X2. bb X0 X1 X2 = (\<exists>Y0. length Y0 = X0 \<and> length (X1 Y0) = X2)"
    by moura
  have f3: "\<forall>n f. finite {na. \<exists>ss. length (ss::'s list) = n \<and> length (f ss::'s list) = na}"
    using output_lengths_finite by blast
  have f4: "\<forall>n f. {na. \<exists>ss. length (ss::'s list) = n \<and> length (f ss::'s list) = na} \<noteq> {}"
    using output_lengths_not_empty by blast
  have f5: "\<forall>ss. thesis \<or> length (f ss) \<noteq> Max {n. \<exists>ssa. length ssa = length ss \<and>
            length (f ssa) = n}"
    using a1 by blast
  have f6: "\<forall>n f. finite (Collect (bb n f))"
    using f3 f2 by presburger
  have f7: "\<forall>n f. Collect (bb n f) \<noteq> {}"
    using f4 f2 by presburger
  have "\<forall>ss. thesis \<or> length (f ss) \<noteq> Max (Collect (bb (length ss) f))"
    using f5 f2 by presburger
  then show ?thesis
    using f7 f6 f2 by (metis Max_in mem_Collect_eq)
qed
end