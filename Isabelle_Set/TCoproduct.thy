\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Coproduct (\<Coprod>-types)\<close>
theory TCoproduct
  imports
    Sets
    HOTG.Coproduct
begin

definition [typedef]: "Coprod A B \<equiv>
  type (\<lambda>x. \<exists>a : A. x = inl a) \<bar> type (\<lambda>x. \<exists>b : B. x = inr b)"

bundle isa_set_coprod_syntax begin notation Coprod (infixl "\<Coprod>" 70) end
bundle no_isa_set_coprod_syntax begin no_notation Coprod (infixl "\<Coprod>" 70) end

unbundle isa_set_coprod_syntax

lemma mem_coprod_iff_Coprod:
  "x \<in> (A \<Coprod> B) \<longleftrightarrow> x : (Element A \<Coprod> Element B)"
  by unfold_types auto

soft_type_translation
  "x \<in> (A \<Coprod> B)" \<rightleftharpoons> "x : (Element A \<Coprod> Element B)"
  using mem_coprod_iff_Coprod by auto

(* TODO: this translation should be automatic whenever it is needed *)
lemma Element_coprod_iff_Coprod:
  "p : Element (A \<Coprod> B) \<longleftrightarrow> p : Element A \<Coprod> Element B"
  using mem_coprod_iff_Coprod by (auto iff: mem_iff_Element)

context
  includes no_hotg_coprod_syntax
begin

lemma CoprodE [elim]:
  assumes "x : A \<Coprod> B"
  obtains (inl) a where "a : A" "x = inl a" | (inr) b where "b : B" "x = inr b"
  using assms unfolding Coprod_def
  by (auto dest!: Union_typeD simp: meaning_of_type)

lemma inl_type [type]: "inl : A \<Rightarrow> (A \<Coprod> B)"
  by unfold_types auto

lemma inr_type [type]: "inr : B \<Rightarrow> (A \<Coprod> B)"
  by unfold_types auto

lemma Dep_Pair_covariant_left:
  "x : A \<Coprod> B \<Longrightarrow> (\<And>x. x : A \<Longrightarrow> x : A') \<Longrightarrow> x : A' \<Coprod> B"
  by auto

lemma Dep_Pair_covariant_right:
  "x : A \<Coprod> B \<Longrightarrow> (\<And>x. x : B \<Longrightarrow> x : B') \<Longrightarrow> x : A \<Coprod> B'"
  by auto

lemma coprod_rec_type [type]: "coprod_rec : (A \<Rightarrow> X) \<Rightarrow> (B \<Rightarrow> X) \<Rightarrow> (A \<Coprod> B) \<Rightarrow> X"
  by unfold_types auto

lemma type_if_inl_self_Coprod: "inl a : A \<Coprod> B \<Longrightarrow> a : A"
  by auto

lemma type_if_inr_self_Coprod: "inr b : A \<Coprod> B \<Longrightarrow> b : B"
  by auto

end


end
