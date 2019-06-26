theory Structure_Examples
imports "../Structure"
begin


subsection \<open>Some structure declarations\<close>

struct magma = "(;; it.
  carrier: non-empty\<cdot>set,
  op: element (it`carrier \<rightarrow> it`carrier \<rightarrow> it`carrier)
;;)"

thm magma_typedef
thm carrier_lbldef


subsection \<open>Monoids\<close>

struct monoid = "(;; it.
  carrier: non-empty\<cdot>set,
  op: element(it`carrier \<rightarrow> it`carrier \<rightarrow> it`carrier),
  e: element(it`carrier)
where
  \<forall>x \<in> it`carrier. it`op`x`e = x \<and> it`op`e`x = x \<and>
  (\<forall>x \<in> it`carrier. \<forall>y \<in> it`carrier. \<forall>z \<in> it`carrier. it`op`x`(it`op`y`z) = it`op`(it`op`x`y)`z)
;;)"


text \<open>Define the additive monoid Z2:\<close>

definition zero ("0") where "0 \<equiv> {}"
definition one ("1") where "1 \<equiv> Succ 0"
definition "Z2 \<equiv> [;;
  carrier := {0, 1},
  op := \<lambda>x \<in> {0, 1}. if x = 0 then \<lambda>y \<in> {0, 1}. y else \<lambda>y \<in> {0,1}. if y = 0 then 1 else 0,
  e := 0
;;]"


lemma "Z2 : monoid"
unfolding monoid_typedef adjective_def
proof (stauto intro_st: Int_typeI)
  oops


end
