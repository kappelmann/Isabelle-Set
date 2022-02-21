theory SOption
  imports Transfer_Test
begin

hide_const sum sum' Sum

definition "unit = {}"
definition "Unit = Element {unit}"

definition "option A \<equiv> {{a} | a \<in> A} \<union> {{}}"
definition "some a = {a}"
definition "none = {}"

abbreviation "Option A \<equiv> Element (option A)"

lemma option_iff: "x \<in> option A \<longleftrightarrow> (\<exists>a\<in>A. x = some a) \<or> x = none"
  unfolding option_def some_def none_def by blast

lemma some_neq_none: "some a \<noteq> none"
  unfolding some_def none_def by simp

lemma some_inject [iff]: "some x = some y \<longleftrightarrow> x = y"
  unfolding some_def by blast

definition "out_some x = (THE a. x = some a)"

lemma out_some [simp]: "out_some (some a) = a"
  unfolding out_some_def some_def by simp

lemma out_some_type: "x \<in> option A \<Longrightarrow> \<exists>a. x = some a \<Longrightarrow> out_some x \<in> A"
  unfolding out_some_def option_def some_def
  by force

definition "option_case s n x = (if x = none then n else s (out_some x))"

lemma case_none [simp]: "option_case s n none = n"
  unfolding option_case_def by simp

lemma case_some [simp]: "option_case s n (some a) = s a"
  unfolding option_case_def
  using out_some some_neq_none by simp

lemma option_case_type':
  "\<lbrakk>\<And>a. a \<in> A \<Longrightarrow> s a \<in> B; n \<in> B; x \<in> (option A)\<rbrakk>
    \<Longrightarrow> option_case s n x \<in> B"
  unfolding option_case_def
  using option_iff by auto

lemma option_case_type:
  "\<lbrakk>s : Element A \<Rightarrow> Element B; n : Element B; x : Option A\<rbrakk>
    \<Longrightarrow> option_case s n x : Element B"
  apply unfold_types
  using option_case_type' by blast

definition "option_in_sum x = option_case (\<lambda>a. inr a) (inl unit) x"

abbreviation "Sum A B \<equiv> Element (coprod A B)"

lemma option_in_sum_type [type]: "option_in_sum : Option A \<Rightarrow> Sum {unit} A"
  apply unfold_types
  unfolding option_in_sum_def
  (* using option_case_type' by (auto intro!: option_case_type') *)
  sorry

interpretation Sum_Unit: set_extension "option A" "coprod {unit} A"  option_in_sum
proof
  show "option_in_sum : Option A \<Rightarrow> Sum {unit} A" by simp
  show "\<forall>x \<in> option A. \<forall>y \<in> option A. option_in_sum x = option_in_sum y \<longrightarrow> x = y"
    unfolding option_in_sum_def
    using option_iff by fastforce
qed

abbreviation "sum_unit \<equiv> Sum_Unit.abs_image"
abbreviation "Sum_Unit A \<equiv> Element (sum_unit A)"

lemmas option_subset_sum_unit [simp] = Sum_Unit.subset_abs_image

corollary [derive]: "x : Option A \<Longrightarrow> x : Sum_Unit A"
  by (unfold_types, rule mem_if_mem_if_subset) auto

end