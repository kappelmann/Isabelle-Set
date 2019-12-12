chapter \<open>Basic category theory\<close>

theory Category
imports Object2

begin

text \<open>
  The soft type of categories is parametrized over the Grothendieck universe in
  which the objects and morphisms live. This allows us to work easily with large
  categories.
\<close>

section \<open>Categories\<close>

(*
  Structure types are easily implemented as set-theoretic function soft types.
  This will be more automated and have dedicated syntax in later iterations. In
  particular, we really need more dependent soft type elaboration.
*)

abbreviation "obj \<C> \<equiv> \<C> @@ obj"
abbreviation hom ("hom\<^bsub>_\<^esub>") where "hom\<^bsub>\<C>\<^esub> A B \<equiv> \<C> @@ hom `A `B"
abbreviation id ("(id\<^bsub>_\<^esub>)") where "id\<^bsub>\<C>\<^esub> A \<equiv> \<C> @@ id `A"
abbreviation comp ("comp\<^bsub>_, _, _, _\<^esub>")
  where "comp\<^bsub>\<C>, A, B, C\<^esub> g f \<equiv> \<C> @@comp `A `B `C `g `f"

definition "Category' U \<equiv>
  type (\<lambda>\<C>.
    obj \<C> : non-empty \<sqdot> subset U \<and>

    \<C> @@ hom \<in> obj \<C> \<rightarrow> obj \<C> \<rightarrow> U \<and>

    \<C> @@ comp \<in>
      \<Prod>A\<in> obj \<C>. \<Prod>B\<in> obj \<C>. \<Prod>C\<in> obj \<C>.
        (hom\<^bsub>\<C>\<^esub> B C \<rightarrow> hom\<^bsub>\<C>\<^esub> A B \<rightarrow> hom\<^bsub>\<C>\<^esub> A C) \<and>

    \<C> @@ id \<in> \<Prod>A\<in> obj \<C>. (hom\<^bsub>\<C>\<^esub> A A) \<and>

    (\<forall>A \<in> obj \<C>. id\<^bsub>\<C>\<^esub> A \<in> hom\<^bsub>\<C>\<^esub> A A) \<and>

    (\<forall>A B \<in> obj \<C>. \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B.
      (comp\<^bsub>\<C>,A,B,B\<^esub> (id\<^bsub>\<C>\<^esub> B) f = f) \<and> (comp\<^bsub>\<C>,A,A,B\<^esub> f (id\<^bsub>\<C>\<^esub> A) = f)) \<and>

    (\<forall>A B C D \<in> obj \<C>.
      \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B. \<forall>g \<in> hom\<^bsub>\<C>\<^esub> B C. \<forall>h \<in> hom\<^bsub>\<C>\<^esub> C D.
        (comp\<^bsub>\<C>,A,B,D\<^esub> (comp\<^bsub>\<C>,B,C,D\<^esub> h g) f) =
          (comp\<^bsub>\<C>,A,C,D\<^esub> h (comp\<^bsub>\<C>,A,B,C\<^esub> g f)))
  )"

definition "Category = Category' V"

definition "Small_Category = Category \<bar> type (\<lambda>\<C>. obj \<C> \<in> V)"


section \<open>The category of sets\<close>

abbreviation (input) "Set_obj  \<equiv> V"
abbreviation (input) "Set_hom  \<equiv> \<lambda>A \<in> V. \<lambda>B \<in> V. A \<rightarrow> B"
abbreviation (input) "Set_id   \<equiv> \<lambda>A \<in> V. \<lambda>x \<in> A. x"
abbreviation (input) "Set_comp \<equiv>
  \<lambda>A \<in> V. \<lambda>B \<in> V. \<lambda>C \<in> V. \<lambda>g \<in> B \<rightarrow> C. \<lambda>f \<in> A \<rightarrow> B. (g \<circ> f)"
  (*Might be nice to have a keyword to define set-theoretic lambdas*)

definition Set_cat ("\<S>et")
  where "\<S>et = {\<langle>@obj, Set_obj\<rangle>, \<langle>@hom, Set_hom\<rangle>, \<langle>@comp, Set_comp\<rangle>, \<langle>@id, Set_id\<rangle>}"

(*These should be generated theorems*)
lemma Set_obj [simp]: "\<S>et @@ obj = Set_obj"
  unfolding Set_cat_def by simp

lemma Set_hom [simp]: "\<S>et @@ hom = Set_hom"
  unfolding Set_cat_def by simp

lemma Set_comp [simp]: "\<S>et @@ comp = Set_comp"
  unfolding Set_cat_def by simp

lemma Set_id [simp]: "\<S>et @@ id = Set_id"
  unfolding Set_cat_def by simp

lemma Set_cat_type [type]: "\<S>et : Category"
  unfolding Category'_def Category_def
  by unfold_types force


section \<open>Functors and natural transformations\<close>

abbreviation obj_map ("_\<^bsub>obj\<^esub>")
  where "\<F>\<^bsub>obj\<^esub> A \<equiv> \<F> @@ obj_map `A"

abbreviation hom_map ("_\<^bsub>hom _ _\<^esub>") where
  "\<F>\<^bsub>hom A B\<^esub> f \<equiv> \<F> @@ hom_map `A `B `f"

(*Future work: auto-elaboration would make definitions like these more convenient:*)
definition "Functor \<C> \<D> \<equiv>
  type (\<lambda>\<F>.
    \<F> @@ obj_map \<in> obj \<C> \<rightarrow> obj \<D> \<and>

    \<F> @@ hom_map \<in>
      \<Prod>A\<in> obj \<C>. \<Prod>B\<in> obj \<C>. (hom\<^bsub>\<C>\<^esub> A B \<rightarrow> hom\<^bsub>\<D>\<^esub> (\<F>\<^bsub>obj\<^esub> A) (\<F>\<^bsub>obj\<^esub> B)) \<and>

    (\<forall>A \<in> obj \<C>. (\<F>\<^bsub>hom A A\<^esub> (id\<^bsub>\<C>\<^esub> A)) = id\<^bsub>\<D>\<^esub> (\<F>\<^bsub>obj\<^esub> A)) \<and>

    (\<forall>A B C \<in> obj \<C>. \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B. \<forall>g \<in> hom\<^bsub>\<C>\<^esub> B C.
      (\<F>\<^bsub>hom (\<F>\<^bsub>obj\<^esub> A) (\<F>\<^bsub>obj\<^esub> C)\<^esub> (comp\<^bsub>\<C>,A,B,C\<^esub> g f)) =
        comp\<^bsub>\<D>,(\<F>\<^bsub>obj\<^esub> A),(\<F>\<^bsub>obj\<^esub> B),(\<F>\<^bsub>obj\<^esub> C)\<^esub> (\<F>\<^bsub>hom B C\<^esub> g) (\<F>\<^bsub>hom A B\<^esub> f))
  )"

definition "Nat_Trans \<C> \<D> \<F> \<G> \<equiv>
  type (\<lambda>\<eta>.
    \<F> : Functor \<C> \<D> \<and>
    \<G> : Functor \<C> \<D> \<and>

    \<eta> \<in> \<Prod>A\<in> obj \<C>. (hom\<^bsub>\<D>\<^esub> (\<F>\<^bsub>obj\<^esub>A) (\<G>\<^bsub>obj\<^esub>A)) \<and>

    (\<forall>A B \<in> obj \<C>. \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B.
      comp\<^bsub>\<D>, \<F>\<^bsub>obj\<^esub>A, \<G>\<^bsub>obj\<^esub>A, \<G>\<^bsub>obj\<^esub>B\<^esub>
        (\<G>\<^bsub>hom (\<G>\<^bsub>obj\<^esub>A) (\<G>\<^bsub>obj\<^esub>B)\<^esub> f)
        (\<eta> `A) =
      comp\<^bsub>\<D>, \<F>\<^bsub>obj\<^esub>A, \<F>\<^bsub>obj\<^esub>B, \<G>\<^bsub>obj\<^esub>B\<^esub>
        (\<eta> `B)
        (\<F>\<^bsub>hom (\<F>\<^bsub>obj\<^esub>A) (\<F>\<^bsub>obj\<^esub>B)\<^esub> f))
  )" \<comment>\<open>This last condition is the commutative square \<open>\<G>f \<circ> \<eta>\<^sub>A = \<eta>\<^sub>B \<circ> \<F>f\<close>\<close>


end
