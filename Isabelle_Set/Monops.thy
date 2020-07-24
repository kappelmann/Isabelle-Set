section \<open>More monotone operators\<close>

theory Monops
imports Monotone

begin

lemma monop_prodI [derive]:
  assumes
    A: "A: Monop (univ X)" and
    B: "B: Monop (univ X)"
  shows
    "(\<lambda>x. A x \<times> B x): Monop (univ X)"
  by (intro MonopI) (auto dest: MonopE[OF A] MonopE[OF B])


end
