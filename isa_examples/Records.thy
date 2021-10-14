theory Records
  imports Main
begin

record point = x :: nat y ::nat

locale wf_point =
fixes pt :: "'a point_scheme" (structure)
assumes xle: "x pt \<le> 100" and yle: "y pt \<le> 100"

datatype color = Brown | Blue | Violet | Purple | Green

value "more \<lparr>x=40, y=20\<rparr>"

record cpoint = point + col :: color

locale wf_cpoint = wf_point +
  assumes wf_col: "col pt \<in> {Blue, Green}"
begin
  lemma "x pt \<le> 100" by (fact xle)
end

record cpoint3 = cpoint + z :: nat

locale wf_cpoint3 = wf_cpoint +
  assumes wf_col3: "col pt = Purple"
      and "z pt \<le> 100"
begin
lemma False using wf_col wf_col3 by simp
end

end