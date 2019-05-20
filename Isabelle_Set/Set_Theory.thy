theory Set_Theory
imports
  Set_Theory_Axioms
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"

begin

subsection \<open>Further notation\<close>

abbreviation not_elem (infixl "\<notin>" 50)
  where "x \<notin> y \<equiv> \<not> x \<in> y"


subsection \<open>Foundational axioms as rules\<close>

lemma empty_rule [simp]: "\<not> x \<in> {}" using empty_axiom by blast

lemmas
  extensionality = extensionality_axiom[rule_format] and
  elem_induct_rule = elem_induct_axiom[rule_format] and
  Union_rule [iff] = Union_axiom[rule_format] and
  Pow_rule [iff] = Pow_axiom[rule_format] and
  Replacement_rule [iff] = Replacement_axiom[rule_format]


subsection \<open>Rules for subsets\<close>

lemma subsetI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  by (simp add: subset_def)

lemma subsetD [elim]: "\<lbrakk>A \<subseteq> B; c \<in> A\<rbrakk> \<Longrightarrow> c \<in> B"
  by (unfold subset_def) auto

lemma subsetCE [elim]: "\<lbrakk>A \<subseteq> B; c \<notin> A \<Longrightarrow> P; c \<in> B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: subset_def, blast)

lemma rev_subsetD: "\<lbrakk>c \<in> A; A \<subseteq> B\<rbrakk> \<Longrightarrow> c \<in> B"
  by blast

lemma contra_subsetD: "\<lbrakk>A \<subseteq> B; c \<notin> B\<rbrakk> \<Longrightarrow> c \<notin> A"
  by blast

lemma rev_contra_subsetD: "\<lbrakk>c \<notin> B; A \<subseteq> B\<rbrakk> \<Longrightarrow> c \<notin> A"
  by blast

lemma subset_refl [simp]: "A \<subseteq> A"
  by blast

lemma subset_trans: "\<lbrakk>A \<subseteq> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> A \<subseteq> C"
  by blast

(* Useful for proving A c= B by rewriting in some cases *)
lemma subset_iff: "A \<subseteq> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B)"
  apply (unfold subset_def)
  apply (rule refl)
  done

text \<open>For calculations:\<close>

declare
  subsetD [trans]
  rev_subsetD [trans]
  subset_trans [trans]


subsection \<open>Rules for equality\<close>

lemma equality_iffI: "(\<And>x. x \<in> A \<longleftrightarrow> x \<in> B) \<Longrightarrow> A = B"
  by (rule extensionality) auto

lemma equalityE: "\<lbrakk>A = B; \<lbrakk>A \<subseteq> B ; B \<subseteq> A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

lemma equalityCE: "\<lbrakk>A = B; \<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> P; \<lbrakk>c \<notin> A; c \<notin> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule equalityE, blast)

lemma equality_iffD: "A = B \<Longrightarrow> (\<And>x. x \<in> A \<longleftrightarrow> x \<in> B)"
  by auto


subsection \<open>Bounded Quantifiers\<close>

definition Ball :: "set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool"
  where "Ball A P \<equiv> (\<forall>x. x \<in> A \<longrightarrow> P x)"

definition Bex :: "set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool"
  where "Bex A P \<equiv> \<exists>x. x \<in> A \<and> P x"

syntax
  "_Set_Ball" :: "[pttrn, set, bool] \<Rightarrow> bool"  ("(3\<forall>_ \<in> _./ _)" 10)
  "_Set_Bex"  :: "[pttrn, set, bool] \<Rightarrow> bool"  ("(3\<exists>_ \<in> _./ _)" 10)
translations
  "\<forall>x \<in> A. P" \<rightleftharpoons> "CONST Ball A (\<lambda>x. P)"
  "\<exists>x \<in> A. P" \<rightleftharpoons> "CONST Bex A (\<lambda>x. P)"


lemma ballI [intro!]: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> \<forall>x \<in> A. P x"
  by (simp add: Ball_def)

lemma bspec [dest?]: "\<lbrakk>\<forall>x \<in> A. P x; x \<in> A\<rbrakk> \<Longrightarrow> P x"
  by (simp add: Ball_def)

lemma rev_ballE [elim]: "\<lbrakk>\<forall>x \<in> A. P x; x \<notin> A \<Longrightarrow> Q; P x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (simp add: Ball_def, blast)

lemma ballE: "\<lbrakk>\<forall>x \<in> A. P x; P x \<Longrightarrow> Q; x \<notin> A \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by blast

(* Trival rewrite rule: \<open>(\<forall>x \<in> A. P) \<longleftrightarrow> P\<close> holds only if A is nonempty! *)
lemma ball_triv [simp]: "(\<forall>x \<in> A. P) \<longleftrightarrow> ((\<exists>x. x \<in> A) \<longrightarrow> P)"
  by (simp add: Ball_def)

lemma ball_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> P x \<longleftrightarrow> P' x\<rbrakk> \<Longrightarrow> (\<forall>x \<in> A. P x) \<longleftrightarrow> (\<forall>x \<in> A'. P' x)"
  by (simp add: Ball_def)

lemma atomize_ball:
  "(\<And>x. x \<in> A \<Longrightarrow> P x) \<equiv> Trueprop (\<forall>x \<in> A. P x)"
  by (simp only: Ball_def atomize_all atomize_imp)

lemmas
  [symmetric, rulify] = atomize_ball and
  [symmetric, defn] = atomize_ball

lemma bexI [intro]: "\<lbrakk>P x; x \<in> A\<rbrakk> \<Longrightarrow> \<exists>x \<in> A. P x"
  by (simp add: Bex_def, blast)

(* The best argument order when there is only one @{term "x \<in> A"} *)
lemma rev_bexI: "\<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> \<exists>x \<in> A. P x"
  by blast

(* Not of the general form for such rules. The existential quantifier becomes universal. *)
lemma bexCI: "\<lbrakk>\<forall>x \<in> A. \<not>P x \<Longrightarrow> P a; a \<in> A\<rbrakk> \<Longrightarrow> \<exists>x \<in> A. P x"
  by blast

lemma bexE [elim!]: "\<lbrakk>\<exists>x \<in> A. P x; \<And>x. \<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (simp add: Bex_def, blast)

(* We do not even have @{term "(\<exists>x \<in> A. True) \<longleftrightarrow> True"} unless @{term "A"} is nonempty *)
lemma bex_triv [simp]: "(\<exists>x \<in> A. P) \<longleftrightarrow> ((\<exists>x. x \<in> A) \<and> P)"
  by (simp add: Bex_def)

lemma bex_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> P x \<longleftrightarrow> P' x\<rbrakk> \<Longrightarrow> (\<exists>x \<in> A. P x) \<longleftrightarrow> (\<exists>x \<in> A'. P' x)"
  by (simp add: Bex_def cong: conj_cong)


subsection \<open>Replacement\<close>

syntax "_Replace"  :: "[set, pttrn, set] => set" ("(1{_ ./ _ \<in> _})")
translations "{y. x \<in> A}" \<rightleftharpoons> "CONST Repl A (\<lambda>x. y)"

lemma RepFunI: "a \<in> A \<Longrightarrow> f a \<in> {f x. x \<in> A}"
  by (unfold Replacement_rule) auto

(* Useful for coinduction proofs *)
lemma RepFun_eqI [intro]: "\<lbrakk>b = f a; a \<in> A\<rbrakk> \<Longrightarrow> b \<in> {f x. x \<in> A}"
  apply (erule ssubst)
  apply (erule RepFunI)
  done

lemma RepFunE [elim!]:
  "\<lbrakk>b \<in> {f x. x \<in> A}; \<And>x.\<lbrakk>x \<in> A; b = f x\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma RepFun_cong [cong]:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> {f x. x \<in> A} = {g x. x \<in> B}"
  by (rule equality_iffI) auto

lemma triv_RepFun [simp]: "{x. x \<in> A} = A"
  by (rule equality_iffI) auto

lemma Repl_empty[iff]: "{f x. x \<in> {}} = {}"
  by (rule equality_iffI) auto

lemma Repl_is_empty[iff]: "{f x. x \<in> A} = {} \<longleftrightarrow> A = {}"
  by (auto dest: equality_iffD intro!: equality_iffI)


subsection \<open>Power set\<close>

lemma PowI: "A \<subseteq> B \<Longrightarrow> A \<in> Pow(B)"
by (erule Pow_rule [THEN iffD2])

lemma PowD: "A \<in> Pow(B) \<Longrightarrow> A \<subseteq> B"
by (erule Pow_rule [THEN iffD1])

lemma Pow_bottom: "{} \<in> Pow A"
  by (auto simp: subset_def)

lemma Pow_top: "A \<in> Pow A"
  by (auto simp: subset_def)


subsection \<open>Rules for the empty set\<close>

lemma emptyE [elim]: "x \<in> {} \<Longrightarrow> P"
  by simp

lemma empty_subsetI [simp]: "{} \<subseteq> A"
  by auto

lemma equals_emptyI [intro]: "\<lbrakk>\<And>y. y \<in> A \<Longrightarrow> False\<rbrakk> \<Longrightarrow> A = {}"
  by (rule extensionality) auto

lemma equals_emptyD [dest]: "A = {} \<Longrightarrow> a \<notin> A"
  by blast

lemma not_emptyI: "a \<in> A \<Longrightarrow> A \<noteq> {}"
  by blast

lemma not_empty_Ex: "A \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A"
  by auto

lemma not_emptyE:
  assumes "A \<noteq> {}"
  obtains x where "x \<in> A"
  using not_empty_Ex[OF assms]
  by auto

lemma subset_empty[simp]: "A \<subseteq> {} \<longleftrightarrow> A = {}"
  by (auto intro: equality_iffI)


subsection \<open>Unordered pairs\<close>

(* text \<open>This is only a low-level construction that should not be used in high-level
proofs.\<close>

definition Upair :: "set \<Rightarrow> set \<Rightarrow> set"
  where "Upair a b = {if i = {} then a else b. i \<in> Pow (Pow {})}" *)

(* private *)
lemma Pow_empty: "x \<in> Pow {} \<longleftrightarrow> x = {}"
  unfolding Pow_rule subset_def
  by auto

(* private *)
lemma Pow_Pow_empty: "x \<in> Pow (Pow {}) \<longleftrightarrow> x = Pow {} \<or> x = {}"
proof
  assume "x \<in> Pow (Pow {})"
  then have subset: "x \<subseteq> Pow {}" ..

  show "x = Pow {} \<or> x = {}"
  proof (cases "{} \<in> x")
    case True
    then have "Pow {} \<subseteq> x"
      by (auto simp: Pow_empty)
    with subset have "x = Pow {}" by (rule extensionality)
    thus ?thesis ..
  next
    case False
    have "x = {}" 
    proof (rule equals0I)
      fix y assume y: "y \<in> x"
      with subset have "y \<in> Pow {}" ..
      with Pow_empty have "y = {}" by simp
      with False y show False by auto
    qed
    thus ?thesis ..
  qed
qed auto

lemma Upair_iff[iff]: "x \<in> Upair a b \<longleftrightarrow> x = a \<or> x = b"
  by (auto simp: Upair_def Pow_Pow_empty)


subsection \<open>Finite sets\<close>

definition Cons :: "set \<Rightarrow> set \<Rightarrow> set"
  where "Cons x A = \<Union>(Upair A (Upair x x))"

lemma Cons_iff[iff]: "y \<in> Cons x A \<longleftrightarrow> y = x \<or> y \<in> A"
  by (auto simp: Cons_def)

lemma consI1 [simp]: "a \<in> Cons a B"
  by simp

lemma consI2: "a \<in> B \<Longrightarrow> a \<in> Cons b B"
  by simp

lemma consE [elim!]: "\<lbrakk>a \<in> Cons b A; a = b \<Longrightarrow> P; a \<in> A \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(*Stronger version of the rule above*)
lemma consE':
    "\<lbrakk>a \<in> Cons b A; a=b \<Longrightarrow> P; \<lbrakk>a \<in> A; a\<noteq>b\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(*Classical introduction rule*)
lemma consCI [intro!]: "(a\<notin>B \<Longrightarrow> a=b) \<Longrightarrow> a \<in> Cons b B"
  by auto

lemma cons_not_0 [simp]: "Cons a B \<noteq> {}"
  by auto

declare cons_not_0 [THEN not_sym, simp]

lemmas cons_neq_0 = cons_not_0 [THEN notE]

(*TODO: [simp]?*)
lemma Cons_commute: "Cons x (Cons y A) = Cons y (Cons x A)"
  by (rule equality_iffI) auto

syntax
  "_Finset_Set" :: "args \<Rightarrow> set"    ("{(_)}")
translations
  "{x, xs}" \<rightleftharpoons> "CONST Cons x {xs}"
  "{x}" \<rightleftharpoons> "CONST Cons x {}"


(*TODO: proper rewrite rules for finite sets! *)


subsection \<open>Set comprehension notation\<close>

text \<open>This is also known as separation.\<close>

definition Collect :: "set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set"
  where "Collect A P \<equiv> \<Union>{if P x then {x} else {} . x \<in> A}"

syntax
  "_Set_Collect" :: "pttrn \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set"  ("(1{_ \<in> _ ./ _})")
translations
  "{x \<in> A. P}" \<rightleftharpoons> "CONST Collect A (\<lambda>x. P)"

lemma Collect_iff[iff]: "x \<in> {y \<in> A. P y} \<longleftrightarrow> x \<in> A \<and> P x"
  by (auto simp: Collect_def)


subsection \<open>General union and intersection\<close>

definition Inter :: "set => set"  ("\<Inter>_" [90] 90)
  where "\<Inter>(A) \<equiv> { x \<in>\<Union>(A) . \<forall>y \<in> A. x \<in>y}"


syntax
  "_UNION" :: "[pttrn, set, set] => set"  ("(3\<Union>_\<in>_./ _)" 10)
  "_INTER" :: "[pttrn, set, set] => set"  ("(3\<Inter>_\<in>_./ _)" 10)
translations
(* @{term"\<Union>x \<in> A. B(x)"} abbreviates @{term"\<Union>({B(x). x \<in> A})"} *)
  "\<Union>x \<in> A. B" \<equiv> "CONST Union {B. x \<in> A}"
  "\<Inter>x \<in> A. B" \<equiv> "CONST Inter {B. x \<in> A}"


subsection\<open>Rules for Unions of families\<close>

lemma UN_iff [iff]: "b \<in> (\<Union>x \<in> A. B(x)) \<longleftrightarrow> (\<exists>x \<in> A. b \<in> B(x))"
by (simp add: Bex_def, blast)

text \<open>The order of the premises presupposes that A is rigid; b may be flexible\<close>

lemma UN_I: "a \<in> A \<Longrightarrow>  b \<in> B a \<Longrightarrow> b \<in>(\<Union>x \<in> A. B(x))"
by (simp, blast)


lemma UN_E [elim!]:
    "\<lbrakk>b \<in> (\<Union>x \<in> A. B(x)); \<And>x.\<lbrakk>x \<in> A; b\<in> B(x)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by blast

lemma UN_cong:
    "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> C(x)=D(x)\<rbrakk> \<Longrightarrow> (\<Union>x \<in> A. C(x)) = (\<Union>x \<in> B. D(x))"
by simp

lemma Inter_iff[iff]: "A \<in> \<Inter>(C) \<longleftrightarrow> (\<forall>x \<in>C. A \<in> x) \<and> C\<noteq>{}"
  unfolding Inter_def Ball_def
  by (force elim: not_emptyE)


text \<open>Intersection is well-behaved only if the family is non-empty!\<close>
lemma InterI [intro!]:
    "\<lbrakk>\<And>x. x \<in> C \<Longrightarrow> A \<in> x; C\<noteq>{}\<rbrakk> \<Longrightarrow> A \<in> \<Inter>(C)"
  by auto

text \<open>A "destruct" rule -- every B in C contains A as an element, but
  A\<in> B can hold when B\<in>C does not!  This rule is analogous to "spec".\<close>
lemma InterD [elim, Pure.elim]: "\<lbrakk>A \<in> \<Inter>(C); B \<in> C\<rbrakk> \<Longrightarrow> A \<in> B"
  by auto

text \<open>"Classical" elimination rule -- does not require exhibiting @{term"B\<in>C"}\<close>

lemma InterE [elim]:
    "\<lbrakk>A \<in> \<Inter>(C); B\<notin>C \<Longrightarrow> R; A\<in> B \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by auto


text \<open> \<open>\<Inter>x \<in> A. B(x)\<close> abbreviates \<open>\<Inter>({B(x). x \<in> A})\<close>\<close>


lemma INT_iff: "b \<in> (\<Inter>x \<in> A. B(x)) \<longleftrightarrow> (\<forall>x \<in> A. b \<in> B(x)) \<and> A \<noteq> {}"
  by auto
  
lemma INT_I: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> b\<in> B(x); A\<noteq>{}\<rbrakk> \<Longrightarrow> b\<in> (\<Inter>x \<in> A. B(x))"
  by blast

lemma INT_E: "\<lbrakk>b \<in> (\<Inter>x \<in> A. B(x)); a \<in> A\<rbrakk> \<Longrightarrow> b \<in> B(a)"
  by blast

lemma INT_cong: "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C(x)=D(x)) \<Longrightarrow> (\<Inter>x \<in> A. C(x)) = (\<Inter>x \<in> B. D(x))"
  by simp


subsection \<open>Binary union and intersection\<close>

definition Un :: "[set, set] \<Rightarrow> set"  (infixl "\<union>" 70)
  where "A \<union> B = \<Union>(Upair A B)"

definition Int :: "[set, set] \<Rightarrow> set"  (infixl "\<inter>" 70)  \<comment> \<open>binary intersection\<close>
  where "A \<inter> B \<equiv> \<Inter>(Upair A B)"

lemma Un_iff[simp]: "x \<in> A \<union> B \<longleftrightarrow> x \<in> A \<or> x \<in> B"
  unfolding Un_def by auto

lemma Int_iff[simp]: "x \<in> A \<inter> B \<longleftrightarrow> x \<in> A \<and> x \<in> B"
  unfolding Int_def by auto

lemma UnI1 [elim?]: "c \<in> A \<Longrightarrow> c \<in> A \<union> B"
  by simp

lemma UnI2 [elim?]: "c \<in> B \<Longrightarrow> c \<in> A \<union> B"
  by simp

lemma UnE [elim!]: "\<lbrakk>c \<in> A \<union> B; c \<in> A \<Longrightarrow> P; c \<in> B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(*Stronger version of the rule above*)
lemma UnE': "\<lbrakk>c \<in> A \<union> B; c \<in> A \<Longrightarrow> P; \<lbrakk>c \<in> B; c\<notin>A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(*Classical introduction rule: no commitment to A vs B*)
lemma UnCI [intro!]: "(c \<notin> B \<Longrightarrow> c \<in> A) \<Longrightarrow> c \<in> A \<union> B"
  by auto


lemma IntI [intro!]: "\<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> c \<in> A \<inter> B"
by simp

lemma IntD1: "c \<in> A \<inter> B \<Longrightarrow> c \<in> A"
by simp

lemma IntD2: "c \<in> A \<inter> B \<Longrightarrow> c \<in> B"
by simp

lemma IntE [elim!]: "\<lbrakk>c \<in> A \<inter> B; \<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by simp



subsection \<open>Set Difference\<close>

definition Diff :: "[set, set] \<Rightarrow> set"  (infixl "\<setminus>" 65)  \<comment> \<open>set difference\<close>
  where "A \<setminus> B \<equiv> { x \<in> A . \<not>(x \<in> B) }"

lemma Diff_iff [simp]: "c \<in> A\<setminus>B \<longleftrightarrow> (c \<in> A \<and> c\<notin>B)"
by (unfold Diff_def, blast)

lemma DiffI [intro!]: "\<lbrakk>c \<in> A; c \<notin> B\<rbrakk> \<Longrightarrow> c \<in> A \<setminus> B"
by simp

lemma DiffD1: "c \<in> A \<setminus> B \<Longrightarrow> c \<in> A"
by simp

lemma DiffD2: "c \<in> A \<setminus> B \<Longrightarrow> c \<notin> B"
by simp

lemma DiffE [elim!]: "\<lbrakk>c \<in> A \<setminus> B; \<lbrakk>c \<in> A; c\<notin>B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by simp



subsection\<open>Consequences of Foundation/elem-Induction\<close>

lemma elem_induct: "(\<And>X. (\<And>x. x \<in> X \<Longrightarrow> P x) \<Longrightarrow> P X) \<Longrightarrow> P A"
  by (insert elem_induct_axiom[of P A]) auto

lemma disjCI2: "(\<not>A \<Longrightarrow> B) \<Longrightarrow> A \<or> B"
  by blast
  
text \<open> Isabelle/ZF's formulation of foundation, for compatibility \<close>
lemma foundation: "A = {} \<or> (\<exists>x \<in> A. \<forall>y\<in>x. y\<notin>A)"
proof (rule disjCI2)
  assume "A \<noteq> {}"
  then obtain x where "x \<in> A" by (rule not_emptyE)
  then show "(\<exists>y \<in> A. \<forall>z\<in>y. z\<notin>A)"
  proof (induct x arbitrary: A rule: elem_induct)
    fix x u assume x: "x \<in> u" 
      and IH: "\<And>z u'. z \<in> x \<Longrightarrow> z \<in> u' \<Longrightarrow> (\<exists>y\<in>u'. \<forall>w\<in>y. w\<notin>u')"
    then show "\<exists>y\<in>u. \<forall>w\<in>y. w\<notin>u"
    proof (cases "\<forall>z\<in>x. z\<notin>u")
      case True from this x show ?thesis by (rule bexI)
    next
      case False
      then obtain y where "y \<in> x" "y \<in> u"
        by (auto elim: not_emptyE)
      then show ?thesis by (rule IH)
    qed
  qed
qed


lemma mem_asym: "\<lbrakk>a \<in> b; \<not>P \<Longrightarrow> b \<in> a\<rbrakk> \<Longrightarrow> P"
apply (rule classical)
apply (rule_tac A1 = "{a,b}" in foundation [THEN disjE])
apply (blast elim!: equalityE)+
done

lemma mem_irrefl: "a \<in> a \<Longrightarrow> P"
by (blast intro: mem_asym)

(*mem_irrefl should NOT be added to default databases:
      it would be tried on most goals, making proofs slower!*)

lemma mem_not_refl: "a \<notin> a"
  by (rule notI) (erule mem_irrefl)

(*Good for proving inequalities by rewriting*)
lemma mem_imp_not_eq: "a \<in> A \<Longrightarrow> a \<noteq> A"
  by (blast elim: mem_irrefl)

lemma eq_imp_not_mem: "a = A \<Longrightarrow> a \<notin> A"
  by (blast elim: mem_irrefl)


end

