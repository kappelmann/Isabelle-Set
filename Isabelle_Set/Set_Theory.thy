section \<open>Higher-order Tarski-Grothendieck set theory\<close>

theory Set_Theory
imports Set_Theory_Axioms

begin

subsection \<open>Preliminaries\<close>

declare [[eta_contract=false]]

abbreviation not_elem (infixl "\<notin>" 50)
  where "x \<notin> y \<equiv> \<not> x \<in> y"


subsection \<open>Foundational axioms as rules\<close>

lemma empty_rule [simp]: "x \<notin> {}" using empty_axiom by blast

lemmas
  extensionality = extensionality_axiom[rule_format] and
  elem_induct_rule = elem_induct_axiom[rule_format] and
  Union_rule [iff] = Union_axiom[rule_format] and
  Pow_rule [iff] = Pow_axiom[rule_format] and
  Replacement_rule [iff] = Replacement_axiom[rule_format]


subsection \<open>Bounded Quantifiers\<close>

definition Ball :: "set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool"
  where "Ball A P \<equiv> (\<forall>x. x \<in> A \<longrightarrow> P x)"

definition Bex :: "set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool"
  where "Bex A P \<equiv> \<exists>x. x \<in> A \<and> P x"

definition Bex1 :: "set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool"
  where "Bex1 A P \<equiv> \<exists>!x. x \<in> A \<and> P x"

syntax
  "_Ball" :: "[pttrn, set, bool] \<Rightarrow> bool"  ("(3\<forall>_ \<in> _./ _)" 10)
  "_Bex"  :: "[pttrn, set, bool] \<Rightarrow> bool"  ("(3\<exists>_ \<in> _./ _)" 10)
  "_Bex1" :: "[pttrn, set, bool] \<Rightarrow> bool"  ("(3\<exists>!_ \<in> _./ _)" 10)
translations
  "\<forall>x \<in> A. P" \<rightleftharpoons> "CONST Ball A (\<lambda>x. P)"
  "\<exists>x \<in> A. P" \<rightleftharpoons> "CONST Bex A (\<lambda>x. P)"
  "\<exists>!x \<in> A. P" \<rightleftharpoons> "CONST Bex1 A (\<lambda>x. P)"


lemma BallI [intro!]: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> \<forall>x \<in> A. P x"
  by (simp add: Ball_def)

lemma Bspec [dest?]: "\<lbrakk>\<forall>x \<in> A. P x; x \<in> A\<rbrakk> \<Longrightarrow> P x"
  by (simp add: Ball_def)

lemma rev_BallE [elim]: "\<lbrakk>\<forall>x \<in> A. P x; x \<notin> A \<Longrightarrow> Q; P x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (simp add: Ball_def, blast)

lemma BallE: "\<lbrakk>\<forall>x \<in> A. P x; P x \<Longrightarrow> Q; x \<notin> A \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by blast

(* LCP: Trival rewrite rule: \<open>(\<forall>x \<in> A. P) \<longleftrightarrow> P\<close> holds only if A is nonempty! *)
lemma Ball_triv [simp]: "(\<forall>x \<in> A. P) \<longleftrightarrow> ((\<exists>x. x \<in> A) \<longrightarrow> P)"
  by (simp add: Ball_def)

lemma Ball_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> P x \<longleftrightarrow> P' x\<rbrakk> \<Longrightarrow> (\<forall>x \<in> A. P x) \<longleftrightarrow> (\<forall>x \<in> A'. P' x)"
  by (simp add: Ball_def)

lemma atomize_Ball:
  "(\<And>x. x \<in> A \<Longrightarrow> P x) \<equiv> Trueprop (\<forall>x \<in> A. P x)"
  by (simp only: Ball_def atomize_all atomize_imp)

lemmas
  [symmetric, rulify] = atomize_Ball and
  [symmetric, defn] = atomize_Ball

lemma BexI [intro]: "\<lbrakk>P x; x \<in> A\<rbrakk> \<Longrightarrow> \<exists>x \<in> A. P x"
  by (simp add: Bex_def, blast)

(* LCP: The best argument order when there is only one @{term "x \<in> A"} *)
lemma rev_BexI: "\<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> \<exists>x \<in> A. P x"
  by blast

(*
  LCP: Not of the general form for such rules. The existential quantifier becomes
  universal.
*)
lemma BexCI: "\<lbrakk>\<forall>x \<in> A. \<not>P x \<Longrightarrow> P a; a \<in> A\<rbrakk> \<Longrightarrow> \<exists>x \<in> A. P x"
  by blast

lemma BexE [elim!]: "\<lbrakk>\<exists>x \<in> A. P x; \<And>x. \<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (simp add: Bex_def, blast)

(*
  LCP: We do not even have @{term "(\<exists>x \<in> A. True) \<longleftrightarrow> True"} unless @{term "A"} is
  nonempty.
*)
lemma Bex_triv [simp]: "(\<exists>x \<in> A. P) \<longleftrightarrow> ((\<exists>x. x \<in> A) \<and> P)"
  by (simp add: Bex_def)

lemma Bex_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> P x \<longleftrightarrow> P' x\<rbrakk> \<Longrightarrow> (\<exists>x \<in> A. P x) \<longleftrightarrow> (\<exists>x \<in> A'. P' x)"
  by (simp add: Bex_def cong: conj_cong)

lemma Bex1I [intro]: "\<lbrakk>P x; x \<in> A; \<And>z. \<lbrakk>P z; z \<in> A\<rbrakk> \<Longrightarrow> z = x\<rbrakk> \<Longrightarrow> \<exists>!x \<in> A. P x"
  by (simp add: Bex1_def, blast)

lemma rev_Bex1I: "\<lbrakk>x \<in> A; P x; \<And>z. \<lbrakk>P z; z \<in> A\<rbrakk> \<Longrightarrow> z = x\<rbrakk> \<Longrightarrow> \<exists>!x \<in> A. P x"
  by blast

lemma Bex1E [elim!]: "\<lbrakk>\<exists>!x \<in> A. P x; \<And>x. \<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (simp add: Bex1_def, blast)

lemma Bex1_triv [simp]: "(\<exists>!x \<in> A. P) \<longleftrightarrow> ((\<exists>!x. x \<in> A) \<and> P)"
  by (auto simp add: Bex1_def)

lemma Bex1_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> P x \<longleftrightarrow> P' x\<rbrakk> \<Longrightarrow> (\<exists>!x \<in> A. P x) \<longleftrightarrow> (\<exists>!x \<in> A'. P' x)"
  by (simp add: Bex1_def cong: conj_cong)

lemma Bex1_implies_Bex: "\<exists>!x \<in> A. P x \<Longrightarrow> \<exists>x \<in> A. P x"
  by auto

lemma ball_conj_distrib:
    "(\<forall>x\<in>A. P x \<and> Q x) \<longleftrightarrow> (\<forall>x\<in>A. P x) \<and> (\<forall>x\<in>A. Q x)"
  by blast


subsection \<open>Subsets\<close>

lemma subsetI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  by (simp add: subset_def)

lemma subsetE [elim]: "\<lbrakk>A \<subseteq> B; c \<in> A\<rbrakk> \<Longrightarrow> c \<in> B"
  by (unfold subset_def) auto

lemma subsetD: "A \<subseteq> B \<Longrightarrow> c \<in> A \<longrightarrow> c \<in> B"
  by auto

lemma subsetCE [elim]: "\<lbrakk>A \<subseteq> B; c \<notin> A \<Longrightarrow> P; c \<in> B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: subset_def, blast)

lemma rev_subsetE: "\<lbrakk>c \<in> A; A \<subseteq> B\<rbrakk> \<Longrightarrow> c \<in> B"
  by auto

lemma contra_subsetE: "\<lbrakk>A \<subseteq> B; c \<notin> B\<rbrakk> \<Longrightarrow> c \<notin> A"
  by blast

lemma rev_contra_subsetE: "\<lbrakk>c \<notin> B; A \<subseteq> B\<rbrakk> \<Longrightarrow> c \<notin> A"
  by auto

lemma subset_refl [simp]: "A \<subseteq> A"
  by blast

lemma subset_trans: "\<lbrakk>A \<subseteq> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> A \<subseteq> C"
  by blast

(* LCP: Useful for proving A \<subseteq> B by rewriting in some cases *)
lemma subset_iff: "A \<subseteq> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B)"
  unfolding subset_def ..

text \<open>For calculations:\<close>

declare
  subsetE [trans]
  rev_subsetE [trans]
  subset_trans [trans]


subsection \<open>Equality\<close>

lemma equality_iffI: "(\<And>x. x \<in> A \<longleftrightarrow> x \<in> B) \<Longrightarrow> A = B"
  by (rule extensionality) auto

lemma equalityE: "\<lbrakk>A = B; \<lbrakk>A \<subseteq> B ; B \<subseteq> A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

lemma equalityCE: "\<lbrakk>A = B; \<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> P; \<lbrakk>c \<notin> A; c \<notin> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule equalityE, blast)

lemma equality_iffD: "A = B \<Longrightarrow> (\<And>x. x \<in> A \<longleftrightarrow> x \<in> B)"
  by auto

lemma equalityI2: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B"
  by (rule extensionality) auto

method extensionality =
  ((rule extensionality)?, auto intro: equality_iffI dest: equality_iffD)
  \<comment>\<open>Frequently used\<close>


subsection \<open>Replacement\<close>

syntax
  "_Replace"  :: "[set, pttrn, set] => set" ("(1{_ |/ _ \<in> _})")
  "_Replace'"  :: "[set, pttrn, set] => set" ("(1{_ ./ _ \<in> _})")
translations
  "{y | x \<in> A}" \<rightleftharpoons> "CONST Repl A (\<lambda>x. y)"
  "{y. x \<in> A}" \<rightharpoonup> "CONST Repl A (\<lambda>x. y)"

lemma ReplI: "a \<in> A \<Longrightarrow> f a \<in> {f x. x \<in> A}"
  by (unfold Replacement_rule) auto

(* LCP: Useful for coinduction proofs *)
lemma RepFun_eqI [intro]: "\<lbrakk>b = f a; a \<in> A\<rbrakk> \<Longrightarrow> b \<in> {f x. x \<in> A}"
  apply (erule ssubst)
  apply (erule ReplI)
  done

(* The converse of the above *)
lemma ReplD:  "b \<in> {f x | x \<in> A} \<Longrightarrow> \<exists>a \<in> A. b = f a"
  by auto

lemma ReplE [elim!]:
  "\<lbrakk>b \<in> {f x. x \<in> A}; \<And>x. \<lbrakk>x \<in> A; b = f x\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma Repl_cong [cong]:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> {f x. x \<in> A} = {g x. x \<in> B}"
  by extensionality

lemma Repl_comp [simp]: "{g b | b \<in> {f a | a \<in> A}} = {g (f a) | a \<in> A}"
  by extensionality

lemma Repl_triv [simp]: "{x. x \<in> A} = A"
  by extensionality

lemma Repl_empty [iff]: "{f x. x \<in> {}} = {}"
  by extensionality

lemma Repl_is_empty [iff]: "{f x. x \<in> A} = {} \<longleftrightarrow> A = {}"
  by (auto dest: equality_iffD intro!: equality_iffI)


subsection \<open>Empty set\<close>

lemma emptyE [elim]: "x \<in> {} \<Longrightarrow> P"
  by auto

lemma empty_subsetI [simp]: "{} \<subseteq> A"
  by auto

lemma equals_emptyI [intro]: "\<lbrakk>\<And>y. y \<in> A \<Longrightarrow> False\<rbrakk> \<Longrightarrow> A = {}"
  by extensionality

lemma equals_emptyD [dest]: "A = {} \<Longrightarrow> a \<notin> A"
  by auto

lemma not_emptyI: "a \<in> A \<Longrightarrow> A \<noteq> {}"
  by auto

lemma not_empty_Ex: "A \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A"
  by auto

lemma not_emptyE:
  assumes "A \<noteq> {}"
  obtains x where "x \<in> A"
  using not_empty_Ex[OF assms]
  by auto

lemma subset_empty[simp]: "A \<subseteq> {} \<longleftrightarrow> A = {}"
  by auto


subsection \<open>Power set\<close>

lemma PowI: "A \<subseteq> B \<Longrightarrow> A \<in> Pow B"
  by auto

lemma PowD: "A \<in> Pow(B) \<Longrightarrow> A \<subseteq> B"
  by auto

lemma Pow_bottom: "{} \<in> Pow A"
  by auto

lemma Pow_top: "A \<in> Pow A"
  by auto

lemma Pow_empty: "x \<in> Pow {} \<longleftrightarrow> x = {}"
  by auto


subsection \<open>Finite sets\<close>

text \<open>
  The unordered pair is defined using replacement. We then use it to define finite sets.
\<close>

definition Upair :: "set \<Rightarrow> set \<Rightarrow> set"
  where "Upair a b = {if i = {} then a else b | i \<in> Pow (Pow {})}"

lemma Upair_elems [iff]: "x \<in> Upair a b \<longleftrightarrow> x = a \<or> x = b"
  by (auto simp: Upair_def)


definition Cons :: "set \<Rightarrow> set \<Rightarrow> set"
  where "Cons x A = \<Union>(Upair A (Upair x x))"

lemma Cons_elems [iff]: "y \<in> Cons x A \<longleftrightarrow> y = x \<or> y \<in> A"
  by (auto simp: Cons_def)

lemma consI1 [simp]: "a \<in> Cons a B"
  by simp

lemma consI2: "a \<in> B \<Longrightarrow> a \<in> Cons b B"
  by simp

lemma consE [elim!]: "\<lbrakk>a \<in> Cons b A; a = b \<Longrightarrow> P; a \<in> A \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(* LCP: Stronger version of the rule above *)
lemma consE':
  "\<lbrakk>a \<in> Cons b A; a = b \<Longrightarrow> P; \<lbrakk>a \<in> A; a \<noteq> b\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(* LCP: Classical introduction rule *)
lemma consCI [intro!]: "(a \<notin> B \<Longrightarrow> a = b) \<Longrightarrow> a \<in> Cons b B"
  by auto

lemma cons_not_empty [simp]: "Cons a B \<noteq> {}"
  by auto

declare cons_not_empty [THEN not_sym, simp]

lemmas cons_neq_empty = cons_not_empty [THEN notE]

(* TODO: [simp]? *)
lemma Cons_commute: "Cons x (Cons y A) = Cons y (Cons x A)"
  by extensionality

syntax
  "_Finset_Set" :: "args \<Rightarrow> set" ("{(_)}")
translations
  "{x, xs}" \<rightleftharpoons> "CONST Cons x {xs}"
  "{x}" \<rightleftharpoons> "CONST Cons x {}"

(* TODO: proper rewrite rules for finite sets! *)

lemma singleton_eq_iff [iff]: "{a} = {b} \<longleftrightarrow> a = b"
  by extensionality

lemma singleton_elem_iff: "x \<in> {a} \<longleftrightarrow> x = a" by auto

lemma singleton_elemD: "x \<in> {a} \<Longrightarrow> x = a" by auto
lemma singleton_elemI: "a \<in> {a}" by auto

lemma Pow_singleton: "Pow {a} = {{}, {a}}"
  by extensionality

corollary Pow_singleton_elems: "x \<in> Pow {a} \<longleftrightarrow> x = {} \<or> x = {a}"
  using Pow_singleton by auto

lemma doubleton_eq_iff: "{a, b} = {c, d} \<longleftrightarrow> (a = c \<and> b = d) \<or> (a = d \<and> b = c)"
  by extensionality

(* Use the following to transfer results about two-element finite sets over to Upairs,
so that there's no difference to the user. *)
lemma Upair_eq_Cons [simp]: "Upair a b = {a, b}"
  by extensionality

subsection \<open>Set comprehension\<close>

text \<open>This is also known as separation.\<close>

definition Collect :: "set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set"
  where "Collect A P \<equiv> \<Union>{if P x then {x} else {} | x \<in> A}"

syntax
  "_Set_Collect" :: "pttrn \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set"  ("(1{_ \<in> _ |/ _})")
  "_Set_Collect'" :: "pttrn \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set"  ("(1{_ \<in> _ ./ _})")
translations
  "{x \<in> A | P}" \<rightleftharpoons> "CONST Collect A (\<lambda>x. P)"
  "{x \<in> A . P}" \<rightharpoonup> "CONST Collect A (\<lambda>x. P)"

lemma Collect_iff [iff]: "x \<in> {y \<in> A. P y} \<longleftrightarrow> x \<in> A \<and> P x"
  by (auto simp: Collect_def)

lemma CollectI [intro]: "\<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> x \<in> {y \<in> A | P y}"
  by auto

lemma CollectD1: "x \<in> {y \<in> A | P y} \<Longrightarrow> x \<in> A"
  by auto

lemma CollectD2: "x \<in> {y \<in> A | P y} \<Longrightarrow> P x"
  by auto

lemma Collect_subset: "Collect A P \<subseteq> A"
  by blast

lemma Collect_cong [cong]:
  "A = B \<Longrightarrow> (\<And>x. x\<in>B ==> P x = Q x) \<Longrightarrow> Collect A P = Collect B Q"
  by (simp add: Collect_def)

lemma Collect_Collect_eq [simp]:
  "Collect (Collect A P) Q = Collect A (\<lambda>x. P x \<and> Q x)"
  by extensionality

lemma Collect_cons:
  "{x\<in>Cons a B. P x} = (if P(a) then Cons a {x\<in>B. P(x)} else {x\<in>B. P(x)})"
  by extensionality

lemma Collect_mono: "A \<subseteq> B \<Longrightarrow> Collect A P \<subseteq> Collect B P"
  by auto

subsection \<open>More replacement\<close>

lemma Repl_singleton: "{f x | x \<in> {a}} = {f a}"
  by extensionality


text \<open>Replacement in predicate form, as in ZF.\<close>

definition Replace :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set"
  where "Replace A P = {THE y. P x y | x \<in> {x \<in> A | \<exists>!y. P x y}}"

syntax
  "_GenRepl"  :: "[pttrn, pttrn, set, bool] => set"  ("(1{_ |/ _ \<in> _, _})")
  "_GenRepl'"  :: "[pttrn, pttrn, set, bool] => set"  ("(1{_ ./ _ \<in> _, _})")
translations
  "{y | x \<in> A, Q}" \<rightleftharpoons> "CONST Replace A (\<lambda>x y. Q)"
  "{y . x \<in> A, Q}" \<rightharpoonup> "CONST Replace A (\<lambda>x y. Q)"


lemma Replace_iff:
  "b \<in> {y | x \<in> A, P x y} \<longleftrightarrow> (\<exists>x \<in> A. P x b \<and> (\<forall>y. P x y \<longrightarrow> y = b))"
proof -
  have "b \<in> {y | x \<in> A, P x y} \<longleftrightarrow> (\<exists>x \<in> A. (\<exists>!y. P x y) \<and> b = (THE y. P x y))"
    using Replace_def by auto
  also have "... \<longleftrightarrow> (\<exists>x \<in> A. P x b \<and> (\<forall>y. P x y \<longrightarrow> y = b))"
  proof (rule Bex_cong[OF refl])
    fix x assume "x \<in> A"
    show
      "(\<exists>!y. P x y) \<and> b = (THE y. P x y) \<longleftrightarrow> P x b \<and> (\<forall>y. P x y \<longrightarrow> y = b)"
      (is "?lhs \<longleftrightarrow> ?rhs")
    proof
      assume "?lhs"
      then have ex1: "\<exists>!y. P x y" and b: "b = (THE y. P x y)" by auto
      show ?rhs
      proof
        from ex1 show "P x b" unfolding b by (rule theI')
        with ex1 show "\<forall>y. P x y \<longrightarrow> y = b" unfolding Ex1_def by blast
      qed
    next
      assume ?rhs
      then have P: "P x b" and uniq: "\<And>y. P x y \<Longrightarrow> y = b" by auto
      show ?lhs
      proof
        from P uniq
        show "\<exists>!y. P x y" by (rule ex1I)
        from this P
        show "b = (THE y. P x y)" by (rule the1_equality[symmetric])
      qed
    qed
  qed
  ultimately show ?thesis by auto
qed

(* Introduction; there must be a unique y such that P x y, namely y = b. *)
lemma ReplaceI [intro]: "\<lbrakk>P x b; x \<in> A; \<And>y. P x y \<Longrightarrow> y = b\<rbrakk> \<Longrightarrow> b \<in> {y | x \<in> A, P x y}"
  by (rule Replace_iff [THEN iffD2], blast)

(* Elimination; may assume there is a unique y such that P x y, namely y = b. *)
lemma ReplaceE:
  "\<lbrakk>b \<in> {y | x \<in> A, P x y}; \<And>x. \<lbrakk>x \<in> A; P x b; \<forall>y. P x y \<longrightarrow> y = b\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (rule Replace_iff [THEN iffD1, THEN BexE], simp+)

(* As above but without the (generally useless) 3rd assumption *)
lemma ReplaceE2 [elim!]:
  "\<lbrakk>b \<in> {y. x \<in> A, P x y}; \<And>x. \<lbrakk>x \<in> A; P x b\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (erule ReplaceE, blast)

lemma Replace_cong [cong]:
  "\<lbrakk>A = B; \<And>x y. x \<in> B \<Longrightarrow> P x y \<longleftrightarrow> Q x y\<rbrakk> \<Longrightarrow> Replace A P = Replace B Q"
  by (rule equality_iffI) (simp add: Replace_iff)


subsection \<open>Union and intersection\<close>

definition Inter :: "set => set"  ("\<Inter>_" [90] 90)
  where "\<Inter>A \<equiv> {x \<in> \<Union>A . \<forall>y \<in> A. x \<in> y}"

lemma Union_empty [simp]: "\<Union>{} = {}"
  by auto

lemma Inter_empty [simp]: "\<Inter>{} = {}"
  unfolding Inter_def by auto

lemma Union_subset_iff: "\<Union>(A) \<subseteq> C \<longleftrightarrow> (\<forall>x\<in>A. x \<subseteq> C)"
  by blast

lemma Union_upper: "B\<in>A ==> B \<subseteq> \<Union>(A)"
  by blast

lemma Union_least: "[| !!x. x\<in>A ==> x\<subseteq>C |] ==> \<Union>(A) \<subseteq> C"
  by blast


syntax
  "_UNION" :: "[pttrn, set, set] => set"  ("(3\<Union>_ \<in> _./ _)" [0, 0, 10]10)
  "_INTER" :: "[pttrn, set, set] => set"  ("(3\<Inter>_ \<in> _./ _)" [0, 0, 10]10)
translations
  \<comment>\<open>@{term "\<Union>x \<in> A. (B x)"} abbreviates @{term "\<Union>({B x. x \<in> A})"}\<close>
  "\<Union>x \<in> A. B" \<rightleftharpoons> "CONST Union {B. x \<in> A}"
  "\<Inter>x \<in> A. B" \<rightleftharpoons> "CONST Inter {B. x \<in> A}"


lemma UN_iff [iff]: "b \<in> (\<Union>x \<in> A. (B x)) \<longleftrightarrow> (\<exists>x \<in> A. b \<in> B x)"
  by (simp add: Bex_def, blast)

text \<open>LCP: The order of the premises presupposes that A is rigid; b may be flexible\<close>

lemma UN_I: "a \<in> A \<Longrightarrow>  b \<in> B a \<Longrightarrow> b \<in> (\<Union>x \<in> A. B x)"
  by (simp, blast)

lemma UN_E [elim!]: "\<lbrakk>b \<in> (\<Union>x \<in> A. B x); \<And>x. \<lbrakk>x \<in> A; b \<in> B x\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by blast

lemma UN_cong: "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> C x = D x\<rbrakk> \<Longrightarrow> (\<Union>x \<in> A. C x) = (\<Union>x \<in> B. D x)"
  by simp

lemma UN_const: "A \<noteq> {} \<Longrightarrow> (\<Union>x \<in> A. B) = B"
  by extensionality

lemma UN_empty_family: "(\<Union>x \<in> {}. B) = {}"
  by auto

lemma UN_empty_sets: "(\<Union>x \<in> A. {}) = {}"
  by auto

lemma Inter_iff [iff]: "A \<in> \<Inter>C \<longleftrightarrow> (\<forall>x \<in> C. A \<in> x) \<and> C \<noteq> {}"
  unfolding Inter_def Ball_def
  by (force elim: not_emptyE)

lemma UN_subset_iff: "(\<Union>x\<in>A. B x) \<subseteq> C \<longleftrightarrow> (\<forall>x\<in>A. B x \<subseteq> C)"
by blast

lemma UN_upper: "x\<in>A \<Longrightarrow> B x \<subseteq> (\<Union>x\<in>A. B x)"
  by blast

lemma UN_least: "[| !!x. x\<in>A ==> B(x)\<subseteq>C |] ==> (\<Union>x\<in>A. B(x)) \<subseteq> C"
by blast

lemma Union_eq_UN: "\<Union>(A) = (\<Union>x\<in>A. x)"
  by auto

lemma Union_is_empty[simp]: "\<Union>A = {} \<longleftrightarrow> A = {} \<or> A = {{}}"
proof
  assume "\<Union>A = {}" show "A = {} \<or> A = {{}}"
  proof (rule disjCI2)
    assume "A \<noteq> {}" then obtain x where "x \<in> A" by auto
    from `\<Union>A = {}` have [simp]: "\<And>x. x \<in> A \<Longrightarrow> x = {}" by auto
    with `x \<in> A` have "x = {}" by simp
    with `x \<in> A` have [simp]: "{} \<in> A" by simp
    show "A = {{}}" by (rule extensionality) auto
  qed
qed auto

lemma Inter_eq_INT: "\<Inter>(A) = (\<Inter>x\<in>A. x)"
  by auto

lemma Inter_subset_iff: "A\<noteq>{}  ==>  C \<subseteq> \<Inter>(A) \<longleftrightarrow> (\<forall>x\<in>A. C \<subseteq> x)"
by blast

lemma Inter_lower: "B\<in>A ==> \<Inter>(A) \<subseteq> B"
by blast

lemma Inter_greatest: "[| A\<noteq>{};  !!x. x\<in>A ==> C\<subseteq>x |] ==> C \<subseteq> \<Inter>(A)"
by blast

(** Intersection of a family of sets  **)

lemma INT_lower: "x\<in>A ==> (\<Inter>x\<in>A. B(x)) \<subseteq> B(x)"
by blast

lemma INT_greatest: "[| A\<noteq>{};  !!x. x\<in>A ==> C\<subseteq>B(x) |] ==> C \<subseteq> (\<Inter>x\<in>A. B(x))"
by force

lemma Union_singleton: "\<Union>({b}) = b"
  by extensionality

lemma Inter_singleton: "\<Inter>({b}) = b"
  by extensionality

lemma UN_0 [simp]: "(\<Union>i \<in> {}. A i) = {}"
  by blast

lemma UN_singleton: "(\<Union>x\<in>A. {x}) = A"
  by extensionality

lemma UN_UN_flatten: "(\<Union>x \<in> (\<Union>y\<in>A. B y). C x) = (\<Union>y\<in>A. \<Union>x\<in>B y. C x)"
  by extensionality

lemma UN_constant [simp]: "(\<Union>y\<in>A. c) = (if A={} then {} else c)"
  by extensionality

lemma INT_constant [simp]: "(\<Inter>y\<in>A. c) = (if A={} then {} else c)"
  by extensionality

lemma UN_RepFun [simp]: "(\<Union>y\<in> Repl A f. B(y)) = (\<Union>x\<in>A. B(f(x)))"
  by auto

lemma INT_RepFun [simp]: "(\<Inter>x\<in>Repl A f. B(x)) = (\<Inter>a\<in>A. B(f(a)))"
  by (auto simp add: Inter_def)

lemma INT_Union_eq: "{} \<notin> A \<Longrightarrow>(\<Inter>x\<in>\<Union>(A). B(x)) = (\<Inter>y\<in>A. \<Inter>x\<in>y. B(x))"
  by (rule equalityI2) (auto)

lemma INT_UN_eq:
  assumes assms: "\<forall>x\<in>A. B x \<noteq> {}"
  shows "(\<Inter>z\<in>(\<Union>x\<in>A. B x). C z) = (\<Inter>x\<in>A. \<Inter>z\<in> B x. C z)"
proof (rule equalityI2) 
  fix x assume "x \<in> (\<Inter>z\<in>(\<Union>x\<in>A. B x). C z)"
  with assms show "x \<in> (\<Inter>x\<in>A. \<Inter>z\<in> B x. C z)" by auto
next
  fix x assume a: "x \<in> (\<Inter>x\<in>A. \<Inter>z\<in> B x. C z)"
  then have "A \<noteq> {}" by auto
  then obtain y where "y \<in> A" by auto
  with assms have "B y \<noteq> {}" by auto
  with `y\<in>A` have "{B x | x \<in> A} \<noteq> {{}}" by extensionality
  with a show "x \<in> (\<Inter>z\<in>(\<Union>x\<in>A. B x). C z)" by auto
qed

text \<open>Intersection is well-behaved only if the family is non-empty!\<close>

lemma InterI [intro!]: "\<lbrakk>\<And>x. x \<in> C \<Longrightarrow> A \<in> x; C \<noteq> {}\<rbrakk> \<Longrightarrow> A \<in> \<Inter>C"
  by auto

(*
  LCP: A "destruct" rule -- every B in C contains A as an element, but A \<in> B can hold
  when B \<in> C does not! This rule is analogous to "spec".
*)
lemma InterD [elim, Pure.elim]: "\<lbrakk>A \<in> \<Inter>C; B \<in> C\<rbrakk> \<Longrightarrow> A \<in> B"
  by auto

(* LCP: "Classical" elimination rule -- does not require exhibiting @{term "B \<in> C"} *)
lemma InterE [elim]: "\<lbrakk>A \<in> \<Inter>C; B \<notin> C \<Longrightarrow> R; A \<in> B \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by auto


text \<open>@{term "\<Inter>x \<in> A. (B x)"} abbreviates @{term "\<Inter>({B x. x \<in> A})"}\<close>

lemma INT_iff: "b \<in> (\<Inter>x \<in> A. B x) \<longleftrightarrow> (\<forall>x \<in> A. b \<in> B x) \<and> A \<noteq> {}"
  by auto
  
lemma INT_I: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> b \<in> B x; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> (\<Inter>x \<in> A. B x)"
  by blast

lemma INT_E: "\<lbrakk>b \<in> (\<Inter>x \<in> A. B x); a \<in> A\<rbrakk> \<Longrightarrow> b \<in> B a"
  by blast

lemma INT_cong: "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> (\<Inter>x \<in> A. C x) = (\<Inter>x \<in> B. D x)"
  by simp


subsection \<open>Binary union and intersection\<close>

definition Un :: "[set, set] \<Rightarrow> set" (infixl "\<union>" 70)
  where "A \<union> B = \<Union>{A, B}"

definition Int :: "[set, set] \<Rightarrow> set" (infixl "\<inter>" 70)
  where "A \<inter> B \<equiv> \<Inter>{A, B}"

lemma Un_iff [simp]: "x \<in> A \<union> B \<longleftrightarrow> x \<in> A \<or> x \<in> B"
  unfolding Un_def by auto

lemma Int_iff [simp]: "x \<in> A \<inter> B \<longleftrightarrow> x \<in> A \<and> x \<in> B"
  unfolding Int_def by auto

lemma UnI1 [elim?]: "c \<in> A \<Longrightarrow> c \<in> A \<union> B"
  by simp

lemma UnI2 [elim?]: "c \<in> B \<Longrightarrow> c \<in> A \<union> B"
  by simp

lemma UnE [elim!]: "\<lbrakk>c \<in> A \<union> B; c \<in> A \<Longrightarrow> P; c \<in> B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(* LCP: Stronger version of the rule above *)
lemma UnE': "\<lbrakk>c \<in> A \<union> B; c \<in> A \<Longrightarrow> P; \<lbrakk>c \<in> B; c \<notin> A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(* LCP: Classical introduction rule: no commitment to A vs B *)
lemma UnCI [intro!]: "(c \<notin> B \<Longrightarrow> c \<in> A) \<Longrightarrow> c \<in> A \<union> B"
  by auto

lemma Un_commute [simp]: "A \<union> B = B \<union> A"
  by extensionality

lemma Un_left_commute: "A \<union> (B \<union> C) = B \<union> (A \<union> C)"
  by extensionality

lemma empty_Un_conv [simp]: "{} \<union> A = A"
  by extensionality

lemma Un_empty_conv [simp]: "A \<union> {} = A"
  by extensionality


lemma Un_subset_iff: "A \<union> B \<subseteq> C \<longleftrightarrow> A \<subseteq> C \<and> B \<subseteq> C"
by blast

lemma Un_upper1: "A \<subseteq> A \<union> B"
by blast

lemma Un_upper2: "B \<subseteq> A \<union> B"
by blast

lemma Un_least: "[| A\<subseteq>C;  B\<subseteq>C |] ==> A \<union> B \<subseteq> C"
by blast

lemma Un_absorb [simp]: "A \<union> A = A"
  by extensionality

lemma Un_left_absorb: "A \<union> (A \<union> B) = A \<union> B"
  by extensionality

lemma Un_assoc: "(A \<union> B) \<union> C  =  A \<union> (B \<union> C)"
  by extensionality

(*Union is an AC-operator*)
lemmas Un_ac = Un_assoc Un_left_absorb Un_commute Un_left_commute

lemma Un_absorb1: "A \<subseteq> B ==> A \<union> B = B"
  by extensionality

lemma Un_absorb2: "B \<subseteq> A ==> A \<union> B = A"
  by extensionality

lemma Un_Int_distrib: "(A \<inter> B) \<union> C  =  (A \<union> C) \<inter> (B \<union> C)"
  by extensionality

lemma subset_Un_iff: "A\<subseteq>B \<longleftrightarrow> A \<union> B = B"
  by extensionality

lemma subset_Un_iff2: "A\<subseteq>B \<longleftrightarrow> B \<union> A = B"
  by extensionality

lemma Un_empty [iff]: "(A \<union> B = {}) \<longleftrightarrow> (A = {} \<and> B = {})"
  by blast

lemma IntI [intro!]: "\<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> c \<in> A \<inter> B"
  by simp

lemma IntD1: "c \<in> A \<inter> B \<Longrightarrow> c \<in> A"
  by simp

lemma IntD2: "c \<in> A \<inter> B \<Longrightarrow> c \<in> B"
  by simp

lemma IntE [elim!]: "\<lbrakk>c \<in> A \<inter> B; \<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma Int_empty_iff [iff]: "(\<forall>a \<in> A. a \<notin> B) \<longleftrightarrow> A \<inter> B = {}"
  by auto

lemma Int_commute [simp]: "A \<inter> B = B \<inter> A"
  by extensionality

lemma Int_subset_iff[simp]: "C \<subseteq> A \<inter> B \<longleftrightarrow> C \<subseteq> A \<and> C \<subseteq> B"
by blast

lemma Int_lower1: "A \<inter> B \<subseteq> A"
by blast

lemma Int_lower2: "A \<inter> B \<subseteq> B"
by blast

lemma Int_greatest: "[| C\<subseteq>A;  C\<subseteq>B |] ==> C \<subseteq> A \<inter> B"
by blast

lemma Int_absorb [simp]: "A \<inter> A = A"
  by extensionality

lemma Int_left_absorb[simp]: "A \<inter> (A \<inter> B) = A \<inter> B"
  by extensionality

lemma Int_left_commute: "A \<inter> (B \<inter> C) = B \<inter> (A \<inter> C)"
  by extensionality

lemma Int_assoc: "(A \<inter> B) \<inter> C  =  A \<inter> (B \<inter> C)"
  by extensionality

(*Intersection is an AC-operator*)
lemmas Int_ac = Int_assoc Int_left_absorb Int_commute Int_left_commute

lemma Int_absorb1: "B \<subseteq> A ==> A \<inter> B = B"
  by extensionality

lemma Int_absorb2: "A \<subseteq> B ==> A \<inter> B = A"
  by extensionality

lemma Int_Un_distrib: "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  by extensionality

lemma Int_Un_distrib2: "(B \<union> C) \<inter> A = (B \<inter> A) \<union> (C \<inter> A)"
  by extensionality

lemma subset_Int_iff: "A\<subseteq>B \<longleftrightarrow> A \<inter> B = A"
  by extensionality

lemma subset_Int_iff2: "A\<subseteq>B \<longleftrightarrow> B \<inter> A = A"
  by extensionality

lemma Un_Int_assoc_iff: "(A \<inter> B) \<union> C = A \<inter> (B \<union> C)  \<longleftrightarrow>  C\<subseteq>A"
  by extensionality

lemma Collect_Un: "Collect (A \<union> B) P = Collect A P \<union> Collect B P"
  by extensionality

lemma Collect_Int: "Collect(A \<inter> B) P = Collect A P \<inter> Collect B P"
  by extensionality


lemma Int_Collect_self_eq: "A \<inter> Collect A P = Collect A P"
  by extensionality

lemma Collect_Int_Collect_eq:
  "Collect A P \<inter> Collect A Q = Collect A (\<lambda>x. P x \<and> Q x)"
  by extensionality

lemma Collect_Union_eq [simp]:
  "Collect (\<Union>x \<in> A. B x) P = (\<Union>x \<in> A. Collect (B x) P)"
  by extensionality

lemma Collect_Int_left: "{x\<in>A. P(x)} \<inter> B = {x \<in> A \<inter> B. P(x)}"
  by extensionality 

lemma Collect_Int_right: "A \<inter> {x\<in>B. P(x)} = {x \<in> A \<inter> B. P(x)}"
  by extensionality 

lemma Collect_disj_eq: "{x\<in>A. P(x) \<or> Q(x)} = Collect A P \<union> Collect A Q"
  by extensionality 

lemma Collect_conj_eq: "{x\<in>A. P(x) \<and> Q(x)} = Collect A P \<inter> Collect A Q" 
  by extensionality 


lemma subset_UN_iff_eq: "A \<subseteq> (\<Union>i\<in>I. B i) \<longleftrightarrow> A = (\<Union>i\<in>I. A \<inter> B i)"
  by extensionality+

lemma Union_Un_distrib: "\<Union>(A \<union> B) = \<Union>(A) \<union> \<Union>(B)"
  by extensionality

lemma Union_Int_subset: "\<Union>(A \<inter> B) \<subseteq> \<Union>(A) \<inter> \<Union>(B)"
by blast

lemma Union_disjoint: "\<Union>(C) \<inter> A = {} \<longleftrightarrow> (\<forall>B\<in>C. B \<inter> A = {})"
by (blast elim!: equalityE)

lemma Union_empty_iff: "\<Union>(A) = {} \<longleftrightarrow> (\<forall>B\<in>A. B={})"
by blast

lemma Int_Union2: "\<Union>(B) \<inter> A = (\<Union>C\<in>B. C \<inter> A)"
  by extensionality

lemma Inter_Un_subset:
     "[| z\<in>A; z\<in>B |] ==> \<Inter>(A) \<union> \<Inter>(B) \<subseteq> \<Inter>(A \<inter> B)"
by blast

lemma Inter_Un_distrib:
     "[| A\<noteq>{};  B\<noteq>{} |] ==> \<Inter>(A \<union> B) = \<Inter>(A) \<inter> \<Inter>(B)"
  by extensionality

lemma UN_Un: "(\<Union>i\<in> A \<union> B. C(i)) = (\<Union>i\<in> A. C(i)) \<union> (\<Union>i\<in>B. C(i))"
  by extensionality

lemma INT_Un: "(\<Inter>i\<in>I \<union> J. A(i)) =
               (if I={} then \<Inter>j\<in>J. A j
                       else if J={} then \<Inter>i\<in>I. A i
                       else ((\<Inter>i\<in>I. A i) \<inter> (\<Inter>j\<in>J. A j)))"
  by extensionality

(*Halmos, Naive Set Theory, page 35.*)
lemma Int_UN_distrib: "B \<inter> (\<Union>i\<in>I. A(i)) = (\<Union>i\<in>I. B \<inter> A(i))"
  by extensionality

lemma Un_INT_distrib: "I\<noteq>{} ==> B \<union> (\<Inter>i\<in>I. A(i)) = (\<Inter>i\<in>I. B \<union> A(i))"
  by extensionality

lemma Int_UN_distrib2:
     "(\<Union>i\<in>I. A(i)) \<inter> (\<Union>j\<in>J. B(j)) = (\<Union>i\<in>I. \<Union>j\<in>J. A(i) \<inter> B(j))"
  by extensionality

lemma Un_INT_distrib2: "[| I\<noteq>{};  J\<noteq>{} |] ==>
      (\<Inter>i\<in>I. A(i)) \<union> (\<Inter>j\<in>J. B(j)) = (\<Inter>i\<in>I. \<Inter>j\<in>J. A(i) \<union> B(j))"
  by extensionality

lemma UN_Un_distrib:
     "(\<Union>i\<in>I. A i \<union> B i) = (\<Union>i\<in>I. A i) \<union> (\<Union>i\<in>I. B i)"
  by extensionality

lemma INT_Int_distrib:
     "I\<noteq>{} ==> (\<Inter>i\<in>I. A(i) \<inter> B(i)) = (\<Inter>i\<in>I. A(i)) \<inter> (\<Inter>i\<in>I. B(i))"
  by extensionality

lemma UN_Int_subset:
     "(\<Union>z\<in>I \<inter> J. A(z)) \<subseteq> (\<Union>z\<in>I. A(z)) \<inter> (\<Union>z\<in>J. A(z))"
by blast



subsection \<open>Set Difference\<close>

definition Diff :: "[set, set] \<Rightarrow> set"  (infixl "\<setminus>" 65)
  where "A \<setminus> B \<equiv> {x \<in> A | x \<notin> B}"

lemma Diff_iff [simp]: "c \<in> A \<setminus> B \<longleftrightarrow> (c \<in> A \<and> c \<notin> B)"
  by (unfold Diff_def, auto)

lemma DiffI [intro!]: "\<lbrakk>c \<in> A; c \<notin> B\<rbrakk> \<Longrightarrow> c \<in> A \<setminus> B"
  by simp

lemma DiffD1: "c \<in> A \<setminus> B \<Longrightarrow> c \<in> A"
  by simp

lemma DiffD2: "c \<in> A \<setminus> B \<Longrightarrow> c \<notin> B"
  by simp

lemma DiffE [elim!]: "\<lbrakk>c \<in> A \<setminus> B; \<lbrakk>c \<in> A; c \<notin> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma Diff_subset: "A\<setminus>B \<subseteq> A"
by blast

lemma Diff_contains: "C\<subseteq>A \<Longrightarrow> C \<inter> B = {} \<Longrightarrow> C \<subseteq> A\<setminus>B"
by blast

lemma Diff_cancel: "A \<setminus> A = {}"
by blast

lemma Diff_triv: "A \<inter> B = {} \<Longrightarrow> A \<setminus> B = A"
  by extensionality

lemma empty_Diff [simp]: "{} \<setminus> A = {}"
  by blast

lemma Diff_0 [simp]: "A \<setminus> {} = A"
  by extensionality

lemma Diff_eq_0_iff: "A \<setminus> B = {} \<longleftrightarrow> A \<subseteq> B"
  by auto

lemma Diff_disjoint: "A \<inter> (B\<setminus>A) = {}"
  by blast

lemma Diff_partition: "A\<subseteq>B \<Longrightarrow> A \<union> (B\<setminus>A) = B"
  by extensionality

lemma subset_Un_Diff: "A \<subseteq> B \<union> (A \<setminus> B)"
by blast

lemma double_complement: "A\<subseteq>B \<Longrightarrow> B\<subseteq>C \<Longrightarrow> B\<setminus>(C\<setminus>A) = A"
  by extensionality

lemma double_complement_Un: "(A \<union> B) \<setminus> (B\<setminus>A) = A"
  by extensionality

lemma Un_Int_crazy:
 "(A \<inter> B) \<union> (B \<inter> C) \<union> (C \<inter> A) = (A \<union> B) \<inter> (B \<union> C) \<inter> (C \<union> A)"
  by extensionality

lemma Diff_Un: "A \<setminus> (B \<union> C) = (A\<setminus>B) \<inter> (A\<setminus>C)"
  by extensionality

lemma Diff_Int: "A \<setminus> (B \<inter> C) = (A\<setminus>B) \<union> (A\<setminus>C)"
  by extensionality

lemma Un_Diff: "(A \<union> B) \<setminus> C = (A \<setminus> C) \<union> (B \<setminus> C)"
  by extensionality

lemma Int_Diff: "(A \<inter> B) \<setminus> C = A \<inter> (B \<setminus> C)"
  by extensionality

lemma Int_Diff_eq: "C\<subseteq>A \<Longrightarrow> ((A \<setminus> B) \<inter> C) = (C \<setminus> B)"
  by extensionality 

lemma Diff_Int_distrib: "C \<inter> (A\<setminus>B) = (C \<inter> A) \<setminus> (C \<inter> B)"
  by extensionality

lemma Diff_Int_distrib2: "(A\<setminus>B) \<inter> C = (A \<inter> C) \<setminus> (B \<inter> C)"
  by extensionality

lemma Diff_UN: "I\<noteq>{} ==> B \<setminus> (\<Union>i\<in>I. A i) = (\<Inter>i\<in>I. B \<setminus> A i)"
  by extensionality

lemma Diff_INT: "I\<noteq>{} ==> B \<setminus> (\<Inter>i\<in>I. A i) = (\<Union>i\<in>I. B \<setminus> A i)"
  by extensionality

lemma Collect_Diff: "Collect (A \<setminus> B) P = Collect A P \<setminus> Collect B P"
  by extensionality



subsection \<open>\<in>-induction\<close>

lemma foundation: "X \<noteq> {} \<Longrightarrow> \<exists>Y \<in> X. Y \<inter> X = {}"
  using elem_induct_axiom[of "\<lambda>x. x \<notin> X"] by auto

lemma foundation2: "X = {} \<or> (\<exists>Y \<in> X. \<forall>y \<in> Y. y \<notin> X)"
  using foundation by blast

lemma elem_asymE: "\<lbrakk>a \<in> b; \<not>P \<Longrightarrow> b \<in> a\<rbrakk> \<Longrightarrow> P"
  apply (rule classical)
  apply (rule_tac X1 = "{a,b}" in foundation2 [THEN disjE])
  apply (blast elim!: equalityE)+
  done

lemma elem_asym: "a \<in> b \<Longrightarrow> b \<notin> a"
  by (auto intro: elem_asymE)

lemma elem_irreflE: "a \<in> a \<Longrightarrow> P"
  by (blast intro: elem_asymE)

text \<open>
LCP: @{thm elem_irreflE} should NOT be added to default databases:
it would be tried on most goals, making proofs slower!
\<close>

lemma elem_irrefl: "a \<notin> a"
  by (rule notI) (erule elem_irreflE)

(* LCP: Good for proving inequalities by rewriting *)
lemma elem_imp_not_eq: "a \<in> A \<Longrightarrow> a \<noteq> A"
  by (blast elim: elem_irreflE)

lemma eq_imp_not_elem: "a = A \<Longrightarrow> a \<notin> A"
  by (blast elim: elem_irreflE)

lemma elem_double_induct:
  fixes X Y :: set
  assumes IH: "\<And>X Y. 
          (\<And>x Y. x \<in> X \<Longrightarrow> P x Y) \<Longrightarrow>
          (\<And>y. y \<in> Y \<Longrightarrow> P X y)
          \<Longrightarrow> P X Y"
  shows "P X Y"
proof (induction X arbitrary: Y rule: elem_induct_rule)
  fix X Y assume 1: "\<And>x Y. x \<in> X \<Longrightarrow> P x Y"
  show "P X Y"
  proof (induction Y rule: elem_induct_rule)
    fix Y assume "\<And>y. y \<in> Y \<Longrightarrow> P X y"
    with 1 show "P X Y" by (rule IH)
  qed
qed

lemma cycle3: 
  assumes "a \<in> b" "b \<in> c" "c \<in> a"
  shows "False"
proof -
  let ?C = "{a, b, c}"
  have "?C \<noteq> {}" by simp
  from foundation[OF this]
  obtain Y where "Y \<in> ?C" "Y \<inter> ?C = {}" by auto
  from `Y \<in> ?C` have "Y = a \<or> Y = b \<or> Y = c" by simp
  thus ?thesis
  proof (elim disjE)
    assume "Y = a"
    with assms have "c \<in> Y \<inter> ?C" by auto
    with `Y \<inter> ?C = {}` show False by auto
  next
    assume "Y = b"
    with assms have "a \<in> Y \<inter> ?C" by auto
    with `Y \<inter> ?C = {}` show False by auto
  next
    assume "Y = c"
    with assms have "b \<in> Y \<inter> ?C" by auto
    with `Y \<inter> ?C = {}` show False by auto
  qed
qed


subsection \<open>Fundamental soft types\<close>

abbreviation set :: "set type"
  where "set \<equiv> any"

definition empty :: "set \<Rightarrow> bool"
  where "empty A \<equiv> A = {}"


subsubsection \<open>Elements of a given set\<close>

definition element :: "set \<Rightarrow> set type"
  where element_typedef: "element A \<equiv> Type (\<lambda>x. x \<in> A)"

lemma element_type_iff [squash]: "x : element A \<longleftrightarrow> x \<in> A"
  unfolding element_typedef by squash_types


subsubsection \<open>Subsets of a given set\<close>

definition subset :: "set \<Rightarrow> set type"
  where subset_typedef[type_simp]: "subset A = element (Pow A)"

lemma subset_type_iff [squash]: "B : subset A \<longleftrightarrow> B \<subseteq> A"
  unfolding element_typedef subset_typedef by squash_types auto


subsubsection \<open>Collections of sets of a given type T\<close>

definition collection :: "set type \<Rightarrow> set type"
  where collection_typedef: "collection T \<equiv> Type (\<lambda>x. \<forall>y \<in> x. y : T)"

(*
  [squash] attribute should be generated automatically for typedefs of the kind T = Type P
*)
lemma collection_type_iff [squash]: "X : collection T \<longleftrightarrow> (\<forall>x \<in> X. x : T)"
  unfolding collection_typedef by squash_types

lemma
  collection_typeI [intro]: "(\<And>x. x \<in> X \<Longrightarrow> x : T) \<Longrightarrow> X : collection T" and
  collection_typeE [elim]: "\<lbrakk>X : collection T; x \<in> X\<rbrakk> \<Longrightarrow> x : T"
  by squash_types auto


subsubsection \<open>Refined types for basic constants\<close>

text \<open>
The following typing rules are less general than what could be proved, since the \<open>bool\<close>
soft type is trivial. But the rules also determine the behavior of type inference.

The rule for HOL.All currently needs to be restricted due to a deficiency in the
elaboration algorithm.
\<close>

lemma
  [type]: "(\<in>) : element A \<Rightarrow> subset A \<Rightarrow> bool" and
  [type]: "Pow : collection T \<Rightarrow> collection (collection T)" and
  [type]: "Union : collection (collection T) \<Rightarrow> collection T" and
  [type]: "Repl : collection T \<Rightarrow> (T \<Rightarrow> S) \<Rightarrow> collection S" and
  
  [type]: "HOL.All : ((T::set type) \<Rightarrow> bool) \<Rightarrow> bool" and
  [type]: "{} : subset A" and
  [type]: "(\<subseteq>) : subset A \<Rightarrow> subset A \<Rightarrow> bool" and
  [type]: "Cons : element A \<Rightarrow> subset A \<Rightarrow> subset A"

  by squash_types auto


text \<open>The following statements are also provable, but not helpful:\<close>

lemma "HOL.All : (Type1 \<Rightarrow> Type2) \<Rightarrow> any"
  by squash_types auto

lemma "(\<in>) : Type1 \<Rightarrow> Type2 \<Rightarrow> bool"
  by squash_types auto


text \<open>
  Some other things that are true, but we do not know yet how to deal with them
  systematically.
\<close>

lemma "A : set \<Longrightarrow> A : collection (element A)"
  by squash_types auto

lemma "A : set \<Longrightarrow> A : subset A"
  by squash_types auto


subsubsection \<open>Types for defined constants\<close>

lemma Un_type [type]: "Un : subset A \<Rightarrow> subset A \<Rightarrow> subset A"
  by squash_types auto

lemma Int_type [type]: "Int: subset A \<Rightarrow> subset A \<Rightarrow> subset A"
  by squash_types auto

lemma Collect_type [type]: "Collect : subset A \<Rightarrow> (element A \<Rightarrow> bool) \<Rightarrow> subset A"
  by squash_types auto


end
