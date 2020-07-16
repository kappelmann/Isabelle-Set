section \<open>Binary natural numbers\<close>

theory Binary
imports Finite_Sets

begin

definition bin_zero where "bin_zero = {}"
definition bin_one  where "bin_one = {{}}"

bundle hotg_bin_zero_syntax begin notation bin_zero ("0\<^sub>2") end
bundle no_hotg_bin_zero_syntax begin no_notation bin_zero ("0\<^sub>2") end

bundle hotg_bin_one_syntax begin notation bin_one ("1\<^sub>2") end
bundle no_hotg_bin_one_syntax begin no_notation bin_one ("1\<^sub>2") end


end
                                                          