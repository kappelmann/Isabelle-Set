chapter \<open>Basic category theory\<close>

theory Category
imports Object

begin

text \<open>
  The soft type of categories is parametrized over the Grothendieck universe in which
  the objects and morphisms live.
  This allows us to work easily with large categories.
\<close>

section \<open>Categories\<close>

(* Josh: First issue: need implicit arguments for structure fields! *)

object ProtoCategory "U :: set" is "\<lparr> (obj @obj) (hom @hom) (comp @comp) (id @id).
  obj  : non-empty \<sqdot> subset U \<and>
  hom  : element (obj \<rightarrow> obj \<rightarrow> U) \<and>
  comp : element (\<Prod>A \<in> obj. \<Prod>B \<in> obj. \<Prod>C \<in> obj. (hom `B `C \<rightarrow> hom `A `B \<rightarrow> hom `A `C)) \<and>
  id   : element (\<Prod>A \<in> obj. (hom `A `A)) \<and>

  \<comment>\<open>Identity morphisms\<close>
  (\<forall>A \<in> obj. id `A \<in> hom `A `A) \<and>

  (\<forall>A \<in> obj. \<forall>B \<in> obj. \<forall>f \<in> hom `A `B.
    (comp `A `A `B `f `(id `A) = f) \<and> (comp `A `B `B `(id `B) `f = f)) \<and>

  \<comment>\<open>Associativity\<close>
  (\<forall>A \<in> obj. \<forall>B \<in> obj. \<forall>C \<in> obj. \<forall>D \<in> obj.
    \<forall>f \<in> hom `A `B. \<forall>g \<in> hom `B `C. \<forall>h \<in> hom `C `D.
      comp `A `B `D `(comp `B `C `D `h `g) `f = comp `A `C `D `h `(comp `A `B` C `g `f))
\<rparr>"

definition Category where
  Category_typedef: "Category = ProtoCategory V"

definition SmallCategory where
  SmallCategory_typedef: "SmallCategory = Category \<bar> \<lparr> (obj @obj). obj \<in> V \<rparr>"

abbreviation obj :: \<open>set \<Rightarrow> set\<close>
  where "obj \<C> \<equiv> \<C>[@obj]"

abbreviation hom :: \<open>set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set\<close> ("hom\<^bsub>_\<^esub>")
  where "hom\<^bsub>\<C>\<^esub> A B \<equiv> \<C>[@hom] `A `B"

abbreviation id :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> ("(id\<^bsub>_\<^esub>)")
  where "id\<^bsub>\<C>\<^esub> A \<equiv> \<C>[@id] `A"

abbreviation comp :: \<open>set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set\<close> ("comp\<^bsub>_, _, _, _\<^esub>")
  where "comp\<^bsub>\<C>, A, B, C\<^esub> g f \<equiv> \<C>[@comp] `A `B `C `g `f"


subsection \<open>The category of sets\<close>

text \<open>Sets in the lowest universe.\<close>

(*
  The following definitions should be automated in a single object/structure definition
  command.
*)
definition "Set_obj  = V"
definition "Set_hom  = \<lambda>A \<in> Set_obj. \<lambda>B \<in> Set_obj. A \<rightarrow> B"
definition "Set_id   = \<lambda>A \<in> Set_obj. \<lambda>x \<in> A. x"
definition "Set_comp =
  \<lambda>A \<in> Set_obj. \<lambda>B \<in> Set_obj. \<lambda>C \<in> Set_obj. \<lambda>g \<in> Set_hom `B `C. \<lambda>f \<in> Set_hom `A `B. (g \<circ> f)"

lemma Set_comp_type [type]:
  "Set_comp : element (\<Prod>A \<in> Set_obj. \<Prod>B \<in> Set_obj. \<Prod>C \<in> Set_obj. (Set_hom `B `C \<rightarrow> Set_hom `A `B \<rightarrow> Set_hom `A `C))"
  unfolding Set_comp_def
  apply unfold_types
  apply (rule lambda_FunctionI)+
  apply (unfold Set_hom_def, simp)
  apply (rule compose_FunctionI)
  apply assumption+
  done
  

definition Set_cat ("\<S>et")
  where "\<S>et = \<lparr> @obj = Set_obj, @hom = Set_hom, @comp = Set_comp, @id = Set_id \<rparr>"

lemma Set_field_simps:
  "\<S>et[@obj]  = Set_obj"
  "\<S>et[@hom]  = Set_hom"
  "\<S>et[@id]   = Set_id"
  "\<S>et[@comp] = Set_comp"
  unfolding Set_cat_def by eval_selector

lemma Set_cat_type: "\<S>et : Category"
unfolding Category_typedef ProtoCategory_def
proof (auto simp: Set_field_simps(* some low-level unfolding *)
  show "Set_obj : non-empty \<sqdot> subset V"
    unfolding Set_obj_def by (discharge_types, rule Univ_nonempty)

  show "Set_hom : element (Set_obj \<rightarrow> Set_obj \<rightarrow> V)"
    unfolding Set_hom_def Set_obj_def by (unfold_types, auto)

  show
    "Set_comp :
      element \<Prod>A \<in> Set_obj. \<Prod>B \<in> Set_obj. \<Prod>C \<in> Set_obj.
        (Set_hom `B `C \<rightarrow> Set_hom `A `B \<rightarrow> Set_hom `A `C)"
    unfolding Set_hom_def Set_obj_def Set_comp_def
    by (unfold_types, auto intro!: lambda_FunctionI simp: beta)

  show "Set_id : element \<Prod>A \<in> Set_obj. (Set_hom `A `A)"
    unfolding Set_id_def Set_obj_def Set_hom_def
    by (unfold_types, auto simp: beta)

  fix A assume
    A: "A \<in> Set_obj"

  thus "Set_id `A \<in> Set_hom `A `A"
    unfolding Set_id_def Set_hom_def by (auto simp: beta)

  fix B assume
    B: "B \<in> Set_obj"
  fix f assume "f \<in> Set_hom `A `B"
  hence
    f: "f \<in> A \<rightarrow> B" by (auto simp: Set_hom_def A B beta)

  note [[auto_elaborate, trace_soft_types]]
  note apply_dep_type [type]
  have
    "Set_comp `? `? `? `f `(Set_id `A) = f" and
    "Set_comp `? `? `? `(Set_id `B) `f = f"
    unfolding Set_hom_def Set_comp_def Set_id_def
    by (auto simp: A B f beta intro: f

  fix C D g h assume
    C: "C \<in> Set_obj" and
    D: "D \<in> Set_obj" and
    "g \<in> Set_hom `B `C" and
    "h \<in> Set_hom `C `D"
  hence
    g: "g \<in> B \<rightarrow> C" and
    h: "h \<in> C \<rightarrow> D" by (auto simp: Set_hom_def B C D beta)

  show
    "Set_comp `A `B `D `(Set_comp `B `C `D `h `g) `f =
      Set_comp `A `C `D `h `(Set_comp `A `B `C `g `f)"
    unfolding Set_comp_def Set_hom_def
    proof (simp add: A B C D f g h beta)
      have *: "h \<circ> g \<in> B \<rightarrow> D" "g \<circ> f \<in> A \<rightarrow> C" using h g f by auto
      show
        "(\<lambda>g \<in> B \<rightarrow> D. \<lambda>x \<in> A \<rightarrow> B. g \<circ> x) `(h \<circ> g) `f =
          (\<lambda>x \<in> A \<rightarrow> C. h \<circ> x) `(g \<circ> f)"
        by (simp add: * beta, subst beta) (auto intro: f g h compose_assoc[symmetric])
    qed
qed


section \<open>Functors, natural transformations\<close>

object Functor "\<C> :: set" "\<D> :: set" is "\<lparr> (obj_map @obj_map) (hom_map @hom_map) .
  obj_map : element (obj \<C> \<rightarrow> obj \<D>) \<and>
  hom_map : element (
    \<Prod>A \<in> obj \<C>. \<Prod>B \<in> obj \<C>. \<Prod>f \<in> hom\<^bsub>\<C>\<^esub> A B.
      (hom\<^bsub>\<D>\<^esub> (obj_map `A) (obj_map `B))) \<and>

  (\<forall>A \<in> obj \<C>. \<forall>B \<in> obj \<C>. \<forall>C \<in> obj \<C>. \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B. \<forall>g \<in> hom\<^bsub>\<C>\<^esub> B C.
    hom_map `A `C `(comp\<^bsub>\<C>, A, B, C\<^esub> g f) =
      comp\<^bsub>\<D>, obj_map `A, obj_map `B, obj_map `C\<^esub> (hom_map `B `C `g) (hom_map `A `B `f)) \<and>

  (\<forall>A \<in> obj \<C>. hom_map `(id\<^bsub>\<C>\<^esub> A) = id\<^bsub>\<D>\<^esub> (obj_map `A))
\<rparr>"

abbreviation obj_map :: "set \<Rightarrow> set \<Rightarrow> set" ("_\<^bsub>obj\<^esub>")
  where "\<F>\<^bsub>obj\<^esub> C \<equiv> \<F>[@obj_map] `C"

abbreviation hom_map :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set" ("_\<^bsub>hom'(_, _')\<^esub>")
  where "\<F>\<^bsub>hom(A, B)\<^esub> f \<equiv> \<F>[@hom_map] `A `B `f"


end
