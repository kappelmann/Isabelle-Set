chapter \<open>Basic category theory\<close>

theory Category
imports Object

begin

text \<open>
  The soft type of categories is parametrized over the Grothendieck universe in
  which the objects and morphisms live. This allows us to work easily with large
  categories.
\<close>

section \<open>Categories\<close>

text \<open>
  Structure types are easily implemented as set-theoretic function soft types.
  This will be more automated and have dedicated syntax in later iterations. In
  particular, we need more dependent soft type elaboration.
\<close>

abbreviation "obj \<C> \<equiv> \<C> @@ obj"
abbreviation hom ("hom\<^bsub>_\<^esub>") where "hom\<^bsub>\<C>\<^esub> A B \<equiv> \<C> @@ hom `A `B"
abbreviation id ("(id\<^bsub>_\<^esub>)") where "id\<^bsub>\<C>\<^esub> A \<equiv> \<C> @@ id `A"
abbreviation comp ("comp\<^bsub>_, _, _, _\<^esub>")
  where "comp\<^bsub>\<C>, A, B, C\<^esub> g f \<equiv> \<C> @@comp `A `B `C `g `f"

definition [typeclass]: "Category' U \<equiv>
  type (\<lambda>\<C>.
    obj \<C>: non-empty \<sqdot> Subset U \<and>

    \<C> @@ hom: obj \<C> \<rightarrow> obj \<C> \<rightarrow> U \<and>

    \<C> @@ comp \<in> \<Prod>A B C\<in> obj \<C>. (hom\<^bsub>\<C>\<^esub> B C \<rightarrow> hom\<^bsub>\<C>\<^esub> A B \<rightarrow> hom\<^bsub>\<C>\<^esub> A C) \<and>

    \<C> @@ id \<in> \<Prod>A\<in> obj \<C>. (hom\<^bsub>\<C>\<^esub> A A) \<and>

    (\<forall>A B \<in> obj \<C>. \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B.
      (comp\<^bsub>\<C>,A,B,B\<^esub> (id\<^bsub>\<C>\<^esub> B) f = f) \<and> (comp\<^bsub>\<C>,A,A,B\<^esub> f (id\<^bsub>\<C>\<^esub> A) = f)) \<and>

    (\<forall>A B C D \<in> obj \<C>. \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B. \<forall>g \<in> hom\<^bsub>\<C>\<^esub> B C. \<forall>h \<in> hom\<^bsub>\<C>\<^esub> C D.
      comp\<^bsub>\<C>,A,B,D\<^esub> (comp\<^bsub>\<C>,B,C,D\<^esub> h g) f =
        comp\<^bsub>\<C>,A,C,D\<^esub> h (comp\<^bsub>\<C>,A,B,C\<^esub> g f))
  )"

definition [typedef]: "Category = Category' V"

definition [typedef]: "Small_Category = Category \<bar> type (\<lambda>\<C>. obj \<C> \<in> V)"

text \<open>
  The following typeclass introduction and elimination rules should be
  automatically generated.
\<close>

lemma Category'I:
  assumes
    "obj \<C>: non-empty \<sqdot> Subset U"

    "\<C> @@ hom: obj \<C> \<rightarrow> obj \<C> \<rightarrow> U"

    "\<C> @@ comp \<in> \<Prod>A B C\<in> obj \<C>. (hom\<^bsub>\<C>\<^esub> B C \<rightarrow> hom\<^bsub>\<C>\<^esub> A B \<rightarrow> hom\<^bsub>\<C>\<^esub> A C)"

    "\<C> @@ id \<in> \<Prod>A\<in> obj \<C>. (hom\<^bsub>\<C>\<^esub> A A)"

    "\<And>A B f. \<lbrakk>A \<in> obj \<C>; B \<in> obj \<C>; f \<in> hom\<^bsub>\<C>\<^esub> A B\<rbrakk>
      \<Longrightarrow> comp\<^bsub>\<C>,A,B,B\<^esub> (id\<^bsub>\<C>\<^esub> B) f = f"

    "\<And>A B f. \<lbrakk>A \<in> obj \<C>; B \<in> obj \<C>; f \<in> hom\<^bsub>\<C>\<^esub> A B\<rbrakk>
      \<Longrightarrow> comp\<^bsub>\<C>,A,A,B\<^esub> f (id\<^bsub>\<C>\<^esub> A) = f"

    "\<And>A B C D f g h.
      \<lbrakk> A \<in> obj \<C>; B \<in> obj \<C>; C \<in> obj \<C>; D \<in> obj \<C>;
        h \<in> hom\<^bsub>\<C>\<^esub> C D; g \<in> hom\<^bsub>\<C>\<^esub> B C; f \<in> hom\<^bsub>\<C>\<^esub> A B \<rbrakk>
      \<Longrightarrow> comp\<^bsub>\<C>,A,B,D\<^esub> (comp\<^bsub>\<C>,B,C,D\<^esub> h g) f =
            comp\<^bsub>\<C>,A,C,D\<^esub> h (comp\<^bsub>\<C>,A,B,C\<^esub> g f)"
  shows
    "\<C>: Category' U"
  unfolding Category'_def
  by (intro has_typeI, (rule, rule assms)+) (fast intro: assms)+

lemma Category'D:
  shows
    "\<C>: Category' U \<Longrightarrow> obj \<C>: non-empty \<sqdot> Subset U"
  and
    "\<C>: Category' U \<Longrightarrow> \<C> @@ hom: obj \<C> \<rightarrow> obj \<C> \<rightarrow> U"
  and
    "\<C>: Category' U \<Longrightarrow>
      \<C> @@ comp \<in> \<Prod>A B C\<in> obj \<C>. (hom\<^bsub>\<C>\<^esub> B C \<rightarrow> hom\<^bsub>\<C>\<^esub> A B \<rightarrow> hom\<^bsub>\<C>\<^esub> A C)"
  and
    "\<C>: Category' U \<Longrightarrow> \<C> @@ id \<in> \<Prod>A\<in> obj \<C>. (hom\<^bsub>\<C>\<^esub> A A)"
  and
    "\<C>: Category' U \<Longrightarrow> \<forall>A B \<in> obj \<C>. \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B.
      (comp\<^bsub>\<C>,A,B,B\<^esub> (id\<^bsub>\<C>\<^esub> B) f = f) \<and> (comp\<^bsub>\<C>,A,A,B\<^esub> f (id\<^bsub>\<C>\<^esub> A) = f)"
  and
    "\<C>: Category' U \<Longrightarrow>
      \<forall>A B C D \<in> obj \<C>. \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B. \<forall>g \<in> hom\<^bsub>\<C>\<^esub> B C. \<forall>h \<in> hom\<^bsub>\<C>\<^esub> C D.
        comp\<^bsub>\<C>,A,B,D\<^esub> (comp\<^bsub>\<C>,B,C,D\<^esub> h g) f =
          comp\<^bsub>\<C>,A,C,D\<^esub> h (comp\<^bsub>\<C>,A,B,C\<^esub> g f)"
  unfolding Category'_def by (drule_tac [1-6] has_typeD) fast+

lemmas CategoryI = Category'I[where ?U=V, folded Category_def]
lemmas CategoryD = Category'D[where ?U=V, folded Category_def]


section \<open>Typing rules\<close>

lemma [type]:
  "obj: Category' U \<Rightarrow> non-empty \<sqdot> Subset U"
  by (rule type_intro) (fact Category'D(1))

lemma [type]:
  "hom: (\<C>: Category' U) \<Rightarrow> Element (obj \<C>) \<Rightarrow> Element (obj \<C>) \<Rightarrow> Element U"
  by (rule type_intro) (auto dest: Category'D(2))

lemma [type]:
  "comp: (\<C>: Category' U) \<Rightarrow>
    (A: Element (obj \<C>)) \<Rightarrow> (B: Element (obj \<C>)) \<Rightarrow> (C: Element (obj \<C>)) \<Rightarrow>
    Element (hom\<^bsub>\<C>\<^esub> B C) \<Rightarrow> Element (hom\<^bsub>\<C>\<^esub> A B) \<Rightarrow> Element (hom\<^bsub>\<C>\<^esub> A C)"
  by (rule type_intro, drule Category'D(3), unfold_types) (rule FunctionE)+
  (*Don't want to have to write "rule FunctionE" all the time!*)

lemma [type]:
  "id: (\<C>: Category' U) \<Rightarrow> (A: Element (obj \<C>)) \<Rightarrow> Element (hom\<^bsub>\<C>\<^esub> A A)"
  by (rule type_intro, drule Category'D(4)) discharge_types


section \<open>The category of sets\<close>

abbreviation (input) "Set_obj  \<equiv> V"
abbreviation (input) "Set_hom  \<equiv> \<lambda>A B \<in> V. A \<rightarrow> B"
abbreviation (input) "Set_id   \<equiv> \<lambda>A \<in> V. \<lambda>x \<in> A. x"
abbreviation (input) "Set_comp \<equiv> \<lambda>A B C \<in> V. \<lambda>g \<in> B \<rightarrow> C. \<lambda>f \<in> A \<rightarrow> B. (g \<circ> f)"

definition Set_cat ("\<S>et") where
  "\<S>et = object {
    \<langle>@obj, Set_obj\<rangle>,
    \<langle>@hom, Set_hom\<rangle>,
    \<langle>@comp, Set_comp\<rangle>,
    \<langle>@id, Set_id\<rangle>
  }"

(*These should be generated theorems*)
lemma [simp]:
  shows Set_cat_obj:  "\<S>et @@ obj = Set_obj"
    and Set_cat_hom:  "\<S>et @@ hom = Set_hom"
    and Set_cat_comp: "\<S>et @@ comp = Set_comp"
    and Set_cat_id:   "\<S>et @@ id = Set_id"
  unfolding Set_cat_def by auto

\<comment> \<open>TODO Kevin: How come id_type needs to be inserted here?\<close>
lemma Set_cat_type [type]: "\<S>et: Category"
  by (rule type_intro, insert id_type, unfold_types) auto


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
      \<Prod>A B\<in> obj \<C>. (hom\<^bsub>\<C>\<^esub> A B \<rightarrow> hom\<^bsub>\<D>\<^esub> (\<F>\<^bsub>obj\<^esub> A) (\<F>\<^bsub>obj\<^esub> B)) \<and>

    (\<forall>A \<in> obj \<C>. (\<F>\<^bsub>hom A A\<^esub> (id\<^bsub>\<C>\<^esub> A)) = id\<^bsub>\<D>\<^esub> (\<F>\<^bsub>obj\<^esub> A)) \<and>

    (\<forall>A B C \<in> obj \<C>. \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B. \<forall>g \<in> hom\<^bsub>\<C>\<^esub> B C.
      (\<F>\<^bsub>hom (\<F>\<^bsub>obj\<^esub> A) (\<F>\<^bsub>obj\<^esub> C)\<^esub> (comp\<^bsub>\<C>,A,B,C\<^esub> g f)) =
        comp\<^bsub>\<D>,(\<F>\<^bsub>obj\<^esub> A),(\<F>\<^bsub>obj\<^esub> B),(\<F>\<^bsub>obj\<^esub> C)\<^esub> (\<F>\<^bsub>hom B C\<^esub> g) (\<F>\<^bsub>hom A B\<^esub> f))
  )"

definition "Nat_Trans \<C> \<D> \<F> \<G> \<equiv>
  type (\<lambda>\<eta>.
    \<F>: Functor \<C> \<D> \<and>
    \<G>: Functor \<C> \<D> \<and>

    \<eta> \<in> \<Prod>A\<in> obj \<C>. (hom\<^bsub>\<D>\<^esub> (\<F>\<^bsub>obj\<^esub>A) (\<G>\<^bsub>obj\<^esub>A)) \<and>

    (\<forall>A B \<in> obj \<C>. \<forall>f \<in> hom\<^bsub>\<C>\<^esub> A B.
      comp\<^bsub>\<D>, \<F>\<^bsub>obj\<^esub>A, \<G>\<^bsub>obj\<^esub>A, \<G>\<^bsub>obj\<^esub>B\<^esub>
        (\<G>\<^bsub>hom (\<G>\<^bsub>obj\<^esub>A) (\<G>\<^bsub>obj\<^esub>B)\<^esub> f)
        (\<eta> `A) =
      comp\<^bsub>\<D>, \<F>\<^bsub>obj\<^esub>A, \<F>\<^bsub>obj\<^esub>B, \<G>\<^bsub>obj\<^esub>B\<^esub>
        (\<eta> `B)
        (\<F>\<^bsub>hom (\<F>\<^bsub>obj\<^esub>A) (\<F>\<^bsub>obj\<^esub>B)\<^esub> f))
  )" \<comment>\<open>This last condition is the commutative square \<open>\<G>f \<circ> \<eta>\<^sub>A = \<eta>\<^sub>B \<circ> \<F>f\<close>\<close>


section \<open>Constructions on categories\<close>

subsection \<open>Product categories\<close>

definition "Product_Cat_obj \<C> \<D> \<equiv> obj \<C> \<times> obj \<D>"

definition "Product_Cat_hom \<C> \<D> \<equiv>
  \<lambda>\<langle>C1, D1\<rangle> \<langle>C2, D2\<rangle>\<in> obj \<C> \<times> obj \<D>. (hom\<^bsub>\<C>\<^esub> C1 C2 \<times> hom\<^bsub>\<D>\<^esub> D1 D2)"

definition "Product_Cat_id \<C> \<D> \<equiv>
  \<lambda>\<langle>C, D\<rangle>\<in> obj \<C> \<times> obj \<D>. \<langle>id\<^bsub>\<C>\<^esub> C, id\<^bsub>\<D>\<^esub> D\<rangle>"

definition "Product_Cat_comp \<C> \<D> \<equiv>
  \<lambda>\<langle>C1, D1\<rangle> \<langle>C2, D2\<rangle> \<langle>C3, D3\<rangle>\<in> Product_Cat_obj \<C> \<D>.
    \<lambda>\<langle>f2, g2\<rangle>\<in> hom\<^bsub>\<C>\<^esub> C2 C3 \<times> hom\<^bsub>\<D>\<^esub> D2 D3.
    \<lambda>\<langle>f1, g1\<rangle>\<in> hom\<^bsub>\<C>\<^esub> C1 C2 \<times> hom\<^bsub>\<D>\<^esub> D1 D2.
      \<langle>comp\<^bsub>\<C>,C1,C2,C3\<^esub> f2 f1, comp\<^bsub>\<D>,D1,D2,D3\<^esub> g2 g1\<rangle>"

definition "Product_Cat \<C> \<D> = object {
  \<langle>@obj, Product_Cat_obj \<C> \<D>\<rangle>,
  \<langle>@hom, Product_Cat_hom \<C> \<D>\<rangle>,
  \<langle>@comp, Product_Cat_comp \<C> \<D>\<rangle>,
  \<langle>@id, Product_Cat_id \<C> \<D>\<rangle>}"

lemma Product_Cat_fields [simp]:
  shows Product_Cat_obj: "(Product_Cat \<C> \<D>) @@ obj = Product_Cat_obj \<C> \<D>"
    and Product_Cat_hom: "(Product_Cat \<C> \<D>) @@ hom = Product_Cat_hom \<C> \<D>"
    and Product_Cat_comp: "(Product_Cat \<C> \<D>) @@ comp = Product_Cat_comp \<C> \<D>"
    and Product_Cat_id: "(Product_Cat \<C> \<D>) @@ id = Product_Cat_id \<C> \<D>"
  unfolding Product_Cat_def by simp_all

lemma Product_Cat_type [derive]:
  assumes
    "\<C>: Category' (univ U)"
    "\<D>: Category' (univ U)"
  shows
    "Product_Cat \<C> \<D>: Category' (univ U)"
proof (rule type_intro, simp_all only: Product_Cat_fields)
  show
    "Product_Cat_obj \<C> \<D>: non-empty \<sqdot> subset (univ U)"
    using Category'D(1)[OF assms(1)] Category'D(1)[OF assms(2)]
    by (auto simp: Product_Cat_obj_def)
  
  show
    "Product_Cat_hom \<C> \<D> \<in>
      Product_Cat_obj \<C> \<D> \<rightarrow> Product_Cat_obj \<C> \<D> \<rightarrow> univ U"
    by (auto simp: Product_Cat_obj_def Product_Cat_hom_def)

  show
    "Product_Cat_comp \<C> \<D> \<in>
      \<Prod>A B C\<in> Product_Cat_obj \<C> \<D>.
        (Product_Cat_hom \<C> \<D> `B `C \<rightarrow>
          Product_Cat_hom \<C> \<D> `A `B \<rightarrow> Product_Cat_hom \<C> \<D> `A `C)"
    unfolding Product_Cat_obj_def Product_Cat_hom_def Product_Cat_comp_def
    by (auto intro!: split_FunctionI simp only: beta_split)

  show
    "Product_Cat_id \<C> \<D> \<in>
      \<Prod>A\<in> Product_Cat_obj \<C> \<D>. (Product_Cat_hom \<C> \<D> `A `A)"
    unfolding Product_Cat_id_def Product_Cat_obj_def Product_Cat_hom_def
    using Category'D(4)[OF assms(1)] Category'D(4)[OF assms(2)]
    by force

  fix A B f assume assms1:
    "A \<in> Product_Cat_obj \<C> \<D>"
    "B \<in> Product_Cat_obj \<C> \<D>"
    "f \<in> Product_Cat_hom \<C> \<D> `A `B"

  show
    "Product_Cat_comp \<C> \<D> `A `B `B `(Product_Cat_id \<C> \<D> `B) `f = f"
    using
      Category'D(5)[OF assms(1)] Category'D(5)[OF assms(2)] assms1
    unfolding
      Product_Cat_obj_def Product_Cat_hom_def Product_Cat_comp_def Product_Cat_id_def
    by (fastforce simp only: beta_split)

  show
    "Product_Cat_comp \<C> \<D> `A `A `B `f `(Product_Cat_id \<C> \<D> `A) = f"
    using
      Category'D(5)[OF assms(1)] Category'D(5)[OF assms(2)] assms1
    unfolding
      Product_Cat_obj_def Product_Cat_hom_def Product_Cat_comp_def Product_Cat_id_def
    by (fastforce simp only: beta_split)

  fix C D h g assume assms2:
    "C \<in> Product_Cat_obj \<C> \<D>"
    "D \<in> Product_Cat_obj \<C> \<D>"
    "h \<in> Product_Cat_hom \<C> \<D> `C `D"
    "g \<in> Product_Cat_hom \<C> \<D> `B `C"

  show
    "Product_Cat_comp \<C> \<D> `A `B `D `(Product_Cat_comp \<C> \<D> `B `C `D `h `g) `f =
       Product_Cat_comp \<C> \<D> `A `C `D `h `(Product_Cat_comp \<C> \<D> `A `B `C `g `f)"
    using
      Category'D(6)[OF assms(1), rule_format]
      Category'D(6)[OF assms(2), rule_format]
      assms1 assms2
    unfolding
      Product_Cat_obj_def Product_Cat_hom_def Product_Cat_comp_def Product_Cat_id_def
    by (auto simp only: beta_split)
qed


end
