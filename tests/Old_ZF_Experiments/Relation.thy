theory Relation
  imports Ordered_Pair ASCII_Syntax
begin

subsection \<open>Relations and Functions\<close>

(*converse of relation r, inverse of function*)
definition converse :: "i \<Rightarrow> i"
  where "converse(r) == {z. w\<in>r, \<exists>x y. w=\<langle>x,y\<rangle> \<and> z=\<langle>y,x\<rangle>}"

definition domain :: "i \<Rightarrow> i"
  where "domain(r) == {x. w\<in>r, \<exists>y. w=\<langle>x,y\<rangle>}"

definition range :: "i \<Rightarrow> i"
  where "range(r) == domain(converse(r))"

definition field :: "i \<Rightarrow> i"
  where "field(r) == domain(r) \<union> range(r)"

definition relation :: "i \<Rightarrow> o"  \<comment> \<open>recognizes sets of pairs\<close>
  where "relation(r) == \<forall>z\<in>r. \<exists>x y. z = \<langle>x,y\<rangle>"


lemma converse_iff [simp]: "<a,b>\<in> converse(r) \<longleftrightarrow> <b,a>\<in>r"
by (unfold converse_def, blast)

lemma converseI [intro!]: "<a,b>\<in>r ==> <b,a>\<in>converse(r)"
by (unfold converse_def, blast)

lemma converseD: "<a,b> \<in> converse(r) ==> <b,a> \<in> r"
by (unfold converse_def, blast)

lemma converseE [elim!]:
    "[| yx \<in> converse(r);
        !!x y. [| yx=<y,x>;  <x,y>\<in>r |] ==> P |]
     ==> P"
by (unfold converse_def, blast)

lemma converse_converse: "r \<subseteq> Sigma A B ==> converse (converse r) = r"
by blast

lemma converse_type: "r\<subseteq>A\<times>B ==> converse(r)\<subseteq>B\<times>A"
by blast

lemma converse_prod [simp]: "converse(A\<times>B) = B\<times>A"
by blast

lemma converse_empty [simp]: "converse({}) = {}"
by blast



end