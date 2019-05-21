section \<open>Relations\<close>

theory Relations
imports Pair

begin

subsection \<open>Relations and functions\<close>

definition relation :: "set \<Rightarrow> bool" \<comment>\<open>recognizes sets of pairs\<close>
  where "relation r \<equiv> \<forall>z \<in> r. \<exists>x y. z = \<langle>x, y\<rangle>"

(* Josh -- Here are good examples of where we want to use soft typing:
the converse should only be defined for relations. *)

(*converse of relation r, inverse of function*)
definition converse :: "set \<Rightarrow> set"
  where "converse(r) == {z | w\<in>r, \<exists>x y. w=\<langle>x,y\<rangle> \<and> z=\<langle>y,x\<rangle>}"

definition domain :: "set \<Rightarrow> set"
  where "domain(r) == {x. w\<in>r, \<exists>y. w=\<langle>x,y\<rangle>}"

definition range :: "set \<Rightarrow> set"
  where "range r = domain (converse r)"

definition field :: "set \<Rightarrow> set"
  where "field r == domain r \<union> range r"



lemma converse_iff [simp]: "\<langle>a,b\<rangle>\<in> converse(r) \<longleftrightarrow> \<langle>b,a\<rangle>\<in>r"
  by (unfold converse_def, blast)

lemma converseI [intro!]: "\<langle>a,b\<rangle>\<in>r \<Longrightarrow> \<langle>b,a\<rangle> \<in> converse r"
  by auto

lemma converseD: "\<langle>a,b\<rangle> \<in> converse(r) \<Longrightarrow> \<langle>b,a\<rangle> \<in> r"
  by auto

lemma converseE [elim!]:
    "\<lbrakk>yx \<in> converse(r);
        \<And>x y. \<lbrakk>yx=\<langle>y,x\<rangle>; \<langle>x,y\<rangle>\<in>r\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
  by (unfold converse_def, blast)

lemma converse_type: "r\<subseteq>A\<times>B \<Longrightarrow> converse(r)\<subseteq>B\<times>A"
by 

(*
TODO

lemma converse_converse: "r \<subseteq> Sigma A B \<Longrightarrow> converse (converse r) = r"
by blast

lemma converse_prod [simp]: "converse(A\<times>B) = B\<times>A"
by blast

lemma converse_empty [simp]: "converse({}) = {}"
by blast
*)

end