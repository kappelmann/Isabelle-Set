section \<open>Basic category theory\<close>

theory Category
imports Object

begin

text \<open>
  The soft type of categories is parametrized over the Grothendieck universe in which
  the objects and morphisms live.
  This allows us to work easily with large categories.
\<close>

object ProtoCategory "U :: set" is "\<lparr> (@obj obj) (@hom hom) (@comp comp) (@id id).
  obj  : non-empty \<sqdot> subset U \<and>
  hom  : element (obj \<rightarrow> obj \<rightarrow> U) \<and>
  comp : element (\<Prod>A \<in> obj. \<Prod>B \<in> obj. \<Prod>C \<in> obj. (hom `A `B \<rightarrow> hom `B `C \<rightarrow> hom `A `C)) \<and>
  id   : element (\<Prod>A \<in> obj. (hom `A `A)) \<and>

  \<comment>\<open>identity morphisms\<close>
  (\<forall>A \<in> obj. id `A \<in> hom `A) \<and>

  (\<forall>A \<in> obj. \<forall>B \<in> obj.
    (\<forall>f \<in> hom `A `B. comp `f `(id `A) = f) \<and> (\<forall>g \<in> hom `B `A. comp `(id `B) `g = g)) \<and>

  \<comment>\<open>associativity\<close>
  (\<forall>A \<in> obj. \<forall>B \<in> obj. \<forall>C \<in> obj. \<forall>D \<in> obj.
    \<forall>f \<in> hom `A `B. \<forall>g \<in> hom `B `C. \<forall>h \<in> hom `C `D.
      comp `(comp `h `g) `f = comp `h `(comp `g `f))
\<rparr>"

definition obj :: \<open>set \<Rightarrow> set\<close> ("obj\<^bsub>_\<^esub>")
  where "obj\<^bsub>C\<^esub> = C[@obj]"

definition hom :: \<open>set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set\<close> ("hom\<^bsub>_\<^esub>")
  where "hom\<^bsub>C\<^esub> A B = C[@hom] `A `B"

definition Category where
  Category_typedef: "Category = ProtoCategory \<V>"

definition SmallCategory where
  SmallCategory_typedef: "SmallCategory = Category \<bar> \<lparr> (@obj obj). obj \<in> \<V> \<rparr>"


subsection \<open>Examples of categories\<close>

text \<open>Sets in the lowest universe.\<close>

definition Set_cat ("\<S>et")
  where "\<S>et = \<lparr>
    @obj = \<V>,
    @hom = \<lambda>A \<in> @obj. \<lambda>B \<in> @obj. (A \<rightarrow> B),
    @comp = \<lambda>A \<in> @obj. \<lambda>B \<in> @obj. \<lambda>C \<in> @obj. \<lambda>f \<in> @hom `A `B. \<lambda>g \<in> @hom `B `C. (g \<circ> f),
    @id = \<lambda>A \<in> @obj. \<lambda>x \<in> @hom `A `A. x
  \<rparr>"

text \<open>Too much low-level manipulation in the following proof...\<close>

declare [[trace_soft_types]]

lemma Set_cat_type: "\<S>et : Category"
unfolding Category_typedef ProtoCategory_typedef
proof auto
  show "\<S>et[@obj] : non-empty \<sqdot> subset \<V>"
    (* Need better beta reduction automation for set-theoretic functions! *)
    apply (simp add: Set_cat_def selector_def; subst apply_cons1)
    apply (auto; strings)
    apply discharge_types
    apply (rule Univ_nonempty)
    done

  show "\<S>et[@hom] : element (\<S>et[@obj] \<rightarrow> \<S>et[@obj] \<rightarrow> \<V>)"
    apply (simp add: Set_cat_def selector_def; (subst (0 2) apply_cons1))
    apply (auto; strings)+
    apply (subst cons_commute, subst apply_cons1)
    apply (auto; strings)+
    apply squash_types
    (* etc. etc. *)
oops


end
