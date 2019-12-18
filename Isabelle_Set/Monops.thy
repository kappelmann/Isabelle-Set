section \<open>More monotone operators\<close>

theory Monops
imports Ordered_Pairs Subset

begin

lemma monop_prodI [derive]:
  assumes
    A: "A : monop (Univ X)" and
    B: "B : monop (Univ X)"
  shows
    "(\<lambda>x. A x \<times> B x) : monop (Univ X)"
  by (intro monopI Univ_prod_subset_closed) (auto dest: monopE[OF A] monopE[OF B])


end
