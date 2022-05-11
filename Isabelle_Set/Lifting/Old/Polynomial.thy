theory Polynomial
  imports Transfer_Test
begin

definition "mono_rep = (\<int> \<setminus> {0}) \<times> \<nat>"
definition "poly_rep = {s \<in> powerset mono_rep | \<forall>m n \<in> s. snd m = snd n \<longrightarrow> fst m = fst n}"

definition "int_in_poly i = (if i = 0 then {} else {\<langle>i, 0\<rangle>})"

lemma
  [type]: "int_in_poly : Element \<int> \<Rightarrow> Element poly_rep"
  unfolding poly_rep_def mono_rep_def int_in_poly_def
  apply unfold_types
  apply auto
  done

interpretation Poly: set_extension \<int> poly_rep int_in_poly
proof
  show "int_in_poly : Integers.Int \<Rightarrow> Element poly_rep" by auto
  show "\<forall>x \<in> \<int>. \<forall>y \<in> \<int>. int_in_poly x = int_in_poly y \<longrightarrow> x = y"
    unfolding int_in_poly_def by auto
qed

abbreviation poly where "poly \<equiv> Poly.abs_image"
abbreviation "Poly \<equiv> Element poly"

lemmas int_subset_poly [simp] = Poly.subset_abs_image

corollary [derive]: "n : Integers.Int \<Longrightarrow> n : Poly"
  by (unfold_types, rule mem_if_mem_if_subset) auto

definition "get_coeff p a = (if (\<exists>m\<in>p. snd p = a) then fst (THE m\<in>p. snd p = a) else 0)"

definition "poly_rep_add p q = \<Union>{
    let a = get_coeff p n in
    let b = get_coeff q n in
    let c = a + b
    in if c = 0 then {} else {\<langle>c, n\<rangle>} | n \<in> \<nat>}"

lemma get_coeff_zero: "get_coeff {} n = 0"
  unfolding get_coeff_def by simp

lemma
  assumes "p \<in> poly_rep" "q \<in> poly_rep"
  shows "poly_rep_add p q \<in> poly_rep"
proof -
  let ?r = "poly_rep_add p q"
  {
    fix x y A B C P
    assume prems: "\<And>x. x \<in> A \<Longrightarrow> x \<in> B" "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> P x y"
    have "A \<in> {C \<in> powerset B | \<forall>x\<in>C. \<forall>y\<in>C. P x y}"
      using prems
      by auto
  }
  note h = this
  { fix m n
    assume prems: "m \<in> ?r" "n \<in> ?r" "snd m = snd n"
    have 1: "\<forall>m\<in>p. \<forall>n\<in>p. snd m = snd n \<longrightarrow> fst m = fst n"
      using assms(1)
      unfolding poly_rep_def mono_rep_def
      by simp
    have 2: "\<forall>m\<in>q. \<forall>n\<in>q. snd m = snd n \<longrightarrow> fst m = fst n"
      using assms(2)
      unfolding poly_rep_def mono_rep_def
      by simp
    obtain f where f: "poly_rep_add = (\<lambda>p q. (\<Union>x\<in> \<nat>. f p q x))"
      using poly_rep_add_def by fastforce
    have h2: "\<And>f g p q. f = (\<lambda> p q. (\<Union>x\<in> \<nat>. g p q x)) \<Longrightarrow> f p q = (\<Union>x\<in> \<nat>. g p q x)" by simp
    have 5: "poly_rep_add p q = (\<Union>x\<in> \<nat>. f p q x)"
      by (rule h2[OF f])
    have 3: "\<And>x. x \<in> \<nat> \<Longrightarrow> f p q x = {} \<or> (\<exists>xl xr. f p q x = {\<langle>xl, xr\<rangle>})"
      using poly_rep_add_def[of p q] 5
      sorry
    have 4: "\<And>x y. x \<in> \<nat> \<Longrightarrow>
            y \<in> \<nat> \<Longrightarrow>
            f p q x \<noteq> {} \<Longrightarrow>
            f p q y \<noteq> {} \<Longrightarrow>
            snd (THE x' \<in> f p q x. True) = snd (THE y' \<in> f p q y. True) \<Longrightarrow>
            x = y"
      sorry
    { fix A B f x y
      assume a1: "\<And>x. x \<in> A \<Longrightarrow> f x = {} \<or> (\<exists>xl xr. f x = {\<langle>xl, xr\<rangle>})"
      and a2: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x \<noteq> {} \<Longrightarrow> f y \<noteq> {} \<Longrightarrow> snd (THE x'\<in>(f x). True) = snd (THE y'\<in>(f y). True) \<Longrightarrow> x = y"
      and a3: "B = (\<Union>x\<in>A. f x)"
      and a4: "x \<in> B"
      and a5: "y \<in> B"
      and a6: "snd x = snd y"
      have "fst x = fst y"
      proof -
        { have "\<not>fst x \<noteq> fst y"
          proof
            assume prem: "fst x \<noteq> fst y"
            obtain x' xl xr where x: "x' \<in> A" "x \<in> f x'" "f x' = {x}" "x = \<langle>xl, xr\<rangle>"
              using prem a1 a3 a4 by fastforce
            obtain y' yl yr where y: "y' \<in> A" "y \<in> f y'" "f y' = {y}" "y = \<langle>yl, yr\<rangle>"
              using prem a1 a3 a5 by fastforce
            have "(THE x \<in> f x'. True) = x" "(THE y \<in> f y'. True) = y"
              using x(3) y(3) by auto
            hence x'_eq_y': "x' = y'"
              using a1 a6 a2[OF x(1) y(1)] x(3, 4) y(3, 4)
              by simp
            moreover have x'_neq_y': "x' \<noteq> y'"
              using x y prem by auto
            ultimately show False by simp
          qed
        }
        note 1 = this
        show ?thesis using 1 by simp
      qed}
    note h1' = this
    have "fst m = fst n"
      using h1'[where ?x3=m and ?y3=n and ?A3=\<nat> and ?fa3="f p q", OF 3 4 _ prems] 3 4 f 5 by blast
  }
  note 1 = this
  { fix m
    assume prem: "m \<in> ?r"
    have "m \<in> mono_rep"
      using assms prem
      unfolding mono_rep_def get_coeff_def
      sorry
  }
  note 2 = this
  show ?thesis
    unfolding poly_rep_def
    apply (rule h)
    using 1 2 by blast+
qed

lemma poly_zero_add_rep: "p \<in> poly_rep \<Longrightarrow> poly_rep_add {} p = p"
  unfolding poly_rep_def poly_rep_add_def
  using get_coeff_zero get_coeff_def
  sorry

definition "poly_add p q = Poly.Abs (poly_rep_add (Poly.Rep p) (Poly.Rep q))"

lemma poly_add_type [type]: "poly_add: Poly \<Rightarrow> Poly \<Rightarrow> Poly"
  unfolding poly_add_def
  sorry

bundle notation_poly_add begin notation poly_add (infixl "+" 65) end
bundle no_notation_poly_add begin no_notation poly_add (infixl "+" 65) end

unbundle
  no_isa_set_int_add_syntax
  notation_poly_add

definition "Poly_Rel p_rep p \<equiv> p \<in> Poly.abs_image \<and> Poly.Rep p = p_rep"

lemma Poly_Rel_0 [transfer_rule]: "Poly_Rel {} 0"
  unfolding Poly.Rep_def Poly_Rel_def Poly.abs_image_def
  using Int_Rel_0 Int_Rel_def int_in_poly_def poly_rep_def
  by simp

lemma Poly_Rel_eq [transfer_rule]: "(Poly_Rel ===> Poly_Rel ===> (=)) (=) (=)"
  unfolding rel_fun_def Poly_Rel_def Poly.Rep_def Poly.abs_image_def
  by (metis Poly.Rep_def Poly.Abs_Rep_inv Poly.abs_image_def)

lemma Poly_Rel_add [transfer_rule]: "(Poly_Rel ===> Poly_Rel ===> Poly_Rel) poly_rep_add poly_add"
  unfolding  rel_fun_def Poly_Rel_def
  using poly_add_def Poly.Rep_Abs_inv poly_add_type
  by (metis (no_types, lifting) ElementD ElementI Dep_fun_typeE)

lemma Poly_Rel_All [transfer_rule]:
  "((Poly_Rel ===> (=)) ===> (=)) (ball poly_rep) (ball poly)"
  unfolding rel_fun_def Poly_Rel_def
  by (smt (verit, ccfv_threshold) ElementD ElementI Dep_fun_typeE Poly.Rep_Abs_inv Poly.Abs_type Poly.Rep_type ball_def)

lemma poly_zero_add: "ball poly (\<lambda>x. 0 + x = x)"
  apply transfer
  using poly_zero_add_rep by simp

end