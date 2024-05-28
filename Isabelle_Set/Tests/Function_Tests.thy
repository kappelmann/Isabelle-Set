theory Function_Tests
  imports
    Isabelle_Set.TSFunctions
    Isabelle_Set.SStrings
begin

lemma beta_should_succeed: "x \<in> A \<Longrightarrow> (\<lambda>x : A. \<langle>x, x\<rangle> :: set)`x = \<langle>x, x\<rangle>" by simp

lemma graph_eval1: "{\<langle>x, y\<rangle>}`x = y" by simp

(*TODO: fix object and function evaluator*)
(* lemma graph_eval2:
  assumes "x1 \<noteq> x2"
  shows "{\<langle>x1, y1\<rangle>, \<langle>x2, y2\<rangle>}`x1 = y1"
  and "{\<langle>x1, y1\<rangle>, \<langle>x2, y2\<rangle>}`x2 = y2"
  using assms by simp_all

lemma graph_eval3:
  assumes "x1 \<noteq> x2" "x2 \<noteq> x3" "x1 \<noteq> x3"
  shows "{\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>,\<langle>x3,y3\<rangle>}`x1 = y1"
  and "{\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>,\<langle>x3,y3\<rangle>}`x2 = y2"
  and "{\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>,\<langle>x3,y3\<rangle>}`x3 = y3"
  using assms by simp_all

lemma graph_eval4:
  assumes "x1 \<noteq> x2" "x2 \<noteq> x3" "x3 \<noteq> x4" "x4 \<noteq> x1" "x2 \<noteq> x4" "x1 \<noteq> x3"
  shows "{\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>,\<langle>x3,y3\<rangle>,\<langle>x4,y4\<rangle>}`x1 = y1"
    and "{\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>,\<langle>x3,y3\<rangle>,\<langle>x4,y4\<rangle>}`x2 = y2"
    and "{\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>,\<langle>x3,y3\<rangle>,\<langle>x4,y4\<rangle>}`x3 = y3"
    and "{\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>,\<langle>x3,y3\<rangle>,\<langle>x4,y4\<rangle>}`x4 = y4"
  using assms by simp_all

lemma labelled_graph_eval4:
  shows "{\<langle>@x1,@y1\<rangle>,\<langle>@x2,@y2\<rangle>,\<langle>@x3,@y3\<rangle>,\<langle>@x4,@y4\<rangle>}`@x1 = @y1"
    and "{\<langle>@x1,@y1\<rangle>,\<langle>@x2,@y2\<rangle>,\<langle>@x3,@y3\<rangle>,\<langle>@x4,@y4\<rangle>}`@x2 = @y2"
    and "{\<langle>@x1,@y1\<rangle>,\<langle>@x2,@y2\<rangle>,\<langle>@x3,@y3\<rangle>,\<langle>@x4,@y4\<rangle>}`@x3 = @y3"
    and "{\<langle>@x1,@y1\<rangle>,\<langle>@x2,@y2\<rangle>,\<langle>@x3,@y3\<rangle>,\<langle>@x4,@y4\<rangle>}`@x4 = @y4"
  by simp_all *)


end
