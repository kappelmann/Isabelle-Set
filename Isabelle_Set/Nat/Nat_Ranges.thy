section \<open>Natural number ranges\<close>
theory Nat_Ranges
  imports Nat_Base
begin

subsection \<open>Ranges\<close>

definition "range_incl_excl l u \<equiv> {i \<in> \<nat> | l \<le> i \<and> i < u}"

bundle isa_set_range_incl_excl_syntax
begin notation range_incl_excl ("[_,\<dots>,_[") end
bundle no_isa_set_range_incl_excl_syntax
begin no_notation range_incl_excl ("[_,\<dots>,_[") end
unbundle isa_set_range_incl_excl_syntax

abbreviation "range_incl_incl l u \<equiv> [l,\<dots>,succ u["

bundle isa_set_range_incl_incl_syntax
begin notation range_incl_incl ("[_,\<dots>,_]") end
bundle no_isa_set_range_incl_incl_syntax
begin no_notation range_incl_incl ("[_,\<dots>,_]") end
unbundle isa_set_range_incl_incl_syntax

abbreviation "range_excl_incl l u \<equiv> [succ l,\<dots>,u]"

bundle isa_set_range_excl_incl_syntax
begin notation range_excl_incl ("]_,\<dots>,_]") end
bundle no_isa_set_range_excl_incl_syntax
begin no_notation range_excl_incl ("]_,\<dots>,_]") end
unbundle isa_set_range_excl_incl_syntax

abbreviation "range_excl_excl l u \<equiv> [succ l,\<dots>,u["

bundle isa_set_range_excl_excl_syntax
begin notation range_excl_excl ("]_,\<dots>,_[") end
bundle no_isa_set_range_excl_excl_syntax
begin no_notation range_excl_excl ("]_,\<dots>,_[") end
unbundle isa_set_range_excl_excl_syntax

bundle isa_set_range_syntax
begin
unbundle
  isa_set_range_incl_excl_syntax
  isa_set_range_incl_incl_syntax
  isa_set_range_excl_incl_syntax
  isa_set_range_excl_excl_syntax
end
bundle no_isa_set_range_syntax
begin
unbundle
  no_isa_set_range_incl_excl_syntax
  no_isa_set_range_incl_incl_syntax
  no_isa_set_range_excl_incl_syntax
  no_isa_set_range_excl_excl_syntax
end

lemma range_incl_excl_type [type]: "range_incl_excl : Nat \<Rightarrow> Nat \<Rightarrow> Subset \<nat>"
  unfolding range_incl_excl_def by unfold_types auto

lemma Nat_mem_rangeI [intro]:
  assumes "u : Nat"
  and "l \<le> n" "n \<le> u"
  shows "n \<in> [l,\<dots>,u]"
  using assms unfolding range_incl_excl_def
  by (auto intro: Nat_lt_succ_if_le Nat_if_le_Nat dest: Nat_if_le_Nat)

lemma mem_rangeE:
  assumes "n \<in> [l,\<dots>,u]"
  obtains "n \<in> \<nat>" "l \<le> n" "n \<le> u"
  using assms unfolding range_incl_excl_def by (auto dest: le_if_lt_succ)

lemma
  assumes "n \<in> [l,\<dots>,u]"
  (*TODO: automatically derive a corresponding type checking rule?*)
  shows mem_nat_if_mem_range: "n \<in> [l,\<dots>,u] \<Longrightarrow> n \<in> \<nat>"
  and ge_if_mem_range: "n \<in> [l,\<dots>,u] \<Longrightarrow> l \<le> n"
  and le_if_mem_range: "n \<in> [l,\<dots>,u] \<Longrightarrow> n \<le> u"
  by (auto elim: mem_rangeE)

lemma Nat_mem_range_zeroI [intro]: "u : Nat \<Longrightarrow> n \<le> u \<Longrightarrow> n \<in> [0,\<dots>,u]"
  by (rule Nat_mem_rangeI) (auto dest: Nat_if_le_Nat)

lemma Nat_mem_range_if_le [intro]: "u : Nat \<Longrightarrow> l \<le> u \<Longrightarrow> l \<in> [l,\<dots>,u]"
  by (rule Nat_mem_rangeI) auto

lemma Nat_mem_range_if_ge [intro]: "u : Nat \<Longrightarrow> l \<le> u \<Longrightarrow> u \<in> [l,\<dots>,u]"
  by (rule Nat_mem_rangeI) auto

lemma Nat_range_subset_if_le_if_le [intro]:
  "u' : Nat \<Longrightarrow> l' \<le> l \<Longrightarrow> u \<le> u' \<Longrightarrow> [l,\<dots>,u] \<subseteq> [l',\<dots>,u']"
  by (intro subsetI Nat_mem_rangeI) (auto elim!: mem_rangeE intro: Nat_le_trans)

lemma Nat_succ_eq_range_zero:
  assumes "n : Nat"
  shows "succ n = [0,\<dots>,n]"
proof -
  have "[0,\<dots>,n] = {i \<in> \<nat> | i \<le> n}"
    unfolding range_incl_excl_def
    by (rule eqI) (auto intro: Nat_lt_succ_if_le le_if_lt_succ)
  then show ?thesis
    using assms unfolding le_def lt_def nat_def
    by (auto dest: ElementD mem_omega_if_mem_if_mem_omega)
qed

(*Note Kevin: should this be intro? should this be backward_derive? what should
it be? If it's intro, it will not be picked when we, for example, want to beta
reduce M `i `j with "M" a matrix. *)
lemma Nat_mem_range_incl_exclI [intro]:
  assumes "n : Nat" "l \<le> n" "n < u"
  shows "n \<in> [l,\<dots>,u["
  using assms unfolding range_incl_excl_def by auto

lemma mem_range_incl_exclE:
  assumes "n \<in> [l,\<dots>,u["
  obtains "n \<in> \<nat>" "n < u" "l \<le> n"
  using assms unfolding range_incl_excl_def by auto

lemma assumes "n \<in> [l,\<dots>,u["
  shows mem_nat_if_mem_range_incl_excl: "n \<in> \<nat>"
  and lt_if_mem_range_incl_excl: "n < u"
  and ge_if_mem_range_incl_excl: "l \<le> n"
  using assms by (auto elim: mem_range_incl_exclE)

(*Note Kevin: maybe a good test for set and type conversion*)
(*lemma
  assumes "l : Nat" "u : Nat" "n : Element [l,\<dots>,u]"
  shows "pred n : Element [pred l,\<dots>,u["
  oops*)

end
