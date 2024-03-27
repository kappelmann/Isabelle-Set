\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Functions on Relations\<close>
theory TSBinary_Relation_Functions
  imports
    HOTG.SBinary_Relation_Functions
    Soft_Types.TBinary_Relation_Functions
    TSBinary_Relations_Base
begin

unbundle no_HOL_ascii_syntax

overloading
  set_rel_restrict_left_type \<equiv> "rel_restrict_left :: set \<Rightarrow> set type \<Rightarrow> set"
  set_rel_restrict_right_type \<equiv> "rel_restrict_right :: set \<Rightarrow> set type \<Rightarrow> set"
begin
  definition "set_rel_restrict_left_type (R :: set) (T :: set type) \<equiv>
    rel_restrict_left R (type_pred T)"
  definition "set_rel_restrict_right_type (R :: set) (T :: set type) \<equiv>
    rel_restrict_right R (type_pred T)"
end

lemma set_rel_restrict_left_type_eq_set_rel_restrict_left_pred [simp]:
  "(R :: set)\<restriction>\<^bsub>T :: set type\<^esub> = R\<restriction>\<^bsub>type_pred T\<^esub>"
  unfolding set_rel_restrict_left_type_def by simp

lemma set_rel_restrict_left_type_eq_set_rel_restrict_left_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "(R :: set)\<restriction>\<^bsub>T :: set type\<^esub> \<equiv> R\<restriction>\<^bsub>P\<^esub>"
  using assms by simp

lemma set_rel_restrict_right_type_eq_set_rel_restrict_right_pred [simp]:
  "(R :: set)\<upharpoonleft>\<^bsub>T :: set type\<^esub> = R\<upharpoonleft>\<^bsub>type_pred T\<^esub>"
  unfolding set_rel_restrict_right_type_def by simp

lemma set_rel_restrict_right_type_eq_set_rel_restrict_right_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "(R :: set)\<upharpoonleft>\<^bsub>T :: set type\<^esub> \<equiv> R\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms by simp

lemma set_restrict_left_type [type]:
  "rel_restrict_left : Dep_Bin_Rel A B \<Rightarrow> (P : Set \<Rightarrow> Bool) \<Rightarrow> Dep_Bin_Rel (A & type P) B"
  by unfold_types force

lemma set_restrict_left_set_type [type]:
  "rel_restrict_left : Dep_Bin_Rel A B \<Rightarrow> (A' : Set) \<Rightarrow> Dep_Bin_Rel (A & Element A') B"
  (*TODO: should be proved with lemma above*)
  by unfold_types force

lemma set_restrict_left_type_type [type]:
  "rel_restrict_left : Dep_Bin_Rel A B \<Rightarrow> (T : Any) \<Rightarrow> Dep_Bin_Rel (A & T) B"
  (*TODO: should be proved with lemma above*)
  by unfold_types force

(*TODO Kevin: restrict_right types + overloaded order constants*)

lemma extend_type [type]:
  "extend : (x : A) \<Rightarrow> B x \<Rightarrow> Dep_Bin_Rel A B \<Rightarrow> Dep_Bin_Rel A B"
  by unfold_types auto

lemma glue_type [type]: "glue : Collection (Dep_Bin_Rel A B) \<Rightarrow> Dep_Bin_Rel A B"
  by unfold_types auto

overloading
  agree_type_set \<equiv> "agree :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "(agree_type_set (T :: set type) :: set \<Rightarrow> _) \<equiv> agree (type_pred T)"
end

lemma agree_type_set_eq_agree_set [simp]:
  "(agree (T :: set type) :: set \<Rightarrow> _) = agree (type_pred T)"
  unfolding agree_type_set_def by simp

lemma agree_type_set_eq_agree_set_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "agree (T :: set type) :: set \<Rightarrow> bool \<equiv> agree P"
  using assms by simp

lemma agree_type_set_iff_agree_set [iff]:
  "agree (T :: set type) (R :: set) \<longleftrightarrow> agree (type_pred T) R"
  by simp

lemma dom_type [type]: "dom : Dep_Bin_Rel A B \<Rightarrow> Collection A"
  by (auto intro: CollectionI)

lemma codom_type: "codom : Dep_Bin_Rel A B \<Rightarrow> Collection (type (\<lambda>y. \<exists>x : A. y : B x))"
  by (auto intro!: CollectionI elim!: Dep_Bin_Rel_memE simp: meaning_of_type)

lemma codom_type' [type]: "codom : Bin_Rel A B \<Rightarrow> Collection B"
  by (auto intro: CollectionI)

lemma set_rel_inv_type:
  "set_rel_inv : Dep_Bin_Rel A B \<Rightarrow> Bin_Rel (type (\<lambda>y. \<exists>x : A. y : B x)) A"
  by unfold_types force

lemma set_rel_inv_type' [type]: "set_rel_inv : Bin_Rel A B \<Rightarrow> Bin_Rel B A"
  by unfold_types auto

lemma Dep_Bin_Rel_mem_set_rel_invE [elim]:
  assumes "R : Dep_Bin_Rel A B"
  and "p \<in> set_rel_inv R"
  obtains x y where "x : A" "y : B x" "\<langle>x, y\<rangle> \<in> R" "p = \<langle>y, x\<rangle>"
  using assms by auto

lemma Dep_Bin_Rel_pair_mem_set_rel_inv_iff [iff]:
  "R : Dep_Bin_Rel A B \<Longrightarrow> \<langle>a, b\<rangle> \<in> set_rel_inv R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  by auto

lemma Dep_Bin_Rel_set_rel_inv_set_rel_inv_eq_self [simp]:
  "R : Dep_Bin_Rel A B \<Longrightarrow> set_rel_inv (set_rel_inv R) = R"
  by (rule eqI) (auto simp: set_rel_inv_inv_eq)

lemma diag_type [type]: "diag : (A : Set) \<Rightarrow> Bin_Rel (Element A) (Element A)"
  by (auto intro: Dep_Bin_RelI)

lemma set_rel_comp_type [type]:
  "set_rel_comp : (S : Bin_Rel B C) \<Rightarrow> (R : Bin_Rel A B) \<Rightarrow> Bin_Rel A C"
  (*FIXME (Kevin)*)
  (* by unfold_types auto *)
  sorry



end