theory compos_1
  imports compos_0 "../2_Mizar/mizar_struct" "../2_Mizar/mizar_string"
   funct_2
begin



mdef COM_Struct :: "Ty"  ("COM-Struct") where
  "struct COM-Struct (# InstructionsF \<rightarrow> (\<lambda>_ . Instructions) #) 
       defined on {InstructionsF}"
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem 
  mlet "S be COM-Struct"
  "cluster  the InstructionsF of S \<rightarrow> Instructions" 
 using field COM_StructE by auto
  
abbreviation compos_1_mode_1 ("Instruction-of _") where
  "Instruction-of S \<equiv> Element-of the InstructionsF of S"

mdef compos_1_def_10 ("halt \<^sub>_" [170] 170) where
  mlet "S be COM-Struct"
  "func halt \<^sub>S \<rightarrow> Instruction-of S equals
     halt the InstructionsF of S"
proof-
  have "the InstructionsF of S be Instructions" by mty auto
  have "halt the InstructionsF of S in the InstructionsF of S" using compos_0_def_10E
   compos_0_def_11 by mauto
  thus "halt the InstructionsF of S be Instruction-of S" using Element_of_rule by mauto
qed

abbreviation Instruction_Sequence ("Instruction-Sequence-of _" [150] 150) where
  "Instruction-Sequence-of S \<equiv> (the InstructionsF of S) -valued \<bar> ManySortedSet-of NAT"

mdef compos_1_def_12 ("_ _:halts'_at _") where
  mlet "S be COM-Struct",
       "p be NAT-defined \<bar>(the InstructionsF of S)-valued\<bar>Function",
       "l be set"
   "pred p S:halts_at l means
     l in dom p \<and> p. l = halt \<^sub>S"..

mtheorem compos_1_def_13:
  mlet "S be COM-Struct",
       "s be Instruction-Sequence-of S",
       "l be Nat"
  "redefine pred s S:halts_at l means
    s. l = halt \<^sub>S"
proof
  have "dom s=NAT" "l in NAT" using partfun_1_def_2E ordinal1_def_12E by mauto
  thus "s S:halts_at l \<longleftrightarrow> s . l = halt \<^sub>S" using compos_1_def_12[of S s l] by auto
qed

end

