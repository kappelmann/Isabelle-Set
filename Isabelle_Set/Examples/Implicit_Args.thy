theory Implicit_Args
  imports "../Pair"
begin


axiomatization
  List :: "set \<Rightarrow> set"
  and Nil :: "set \<Rightarrow> set"
  and Cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  and append :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where
    Nil_type[type implicit: 1]: "Nil : (A: set) \<Rightarrow> element (List A)"
    and Cons_type[type implicit: 1]: "Cons : (A: set) \<Rightarrow> element A \<Rightarrow> element (List A) \<Rightarrow> element (List A)" 
    and append_type[type implicit: 1]: "append : (A: set) \<Rightarrow> element (List A) \<Rightarrow> element (List A) \<Rightarrow> element (List A)"


ML \<open>


fun insert_dummies implicit_table (t as Const (n, _)) =
      list_comb (t, map (fn n => Implicit_Arguments.mk_iarg n dummyT) (implicit_table n))
  | insert_dummies _ t = t

val insert_implicits = Term.map_aterms (insert_dummies (Soft_Type_Context.get_implicits (Context.Proof \<^context>)))
\<close>


ML \<open>

fun do_mark m t = Const ("_mark_" ^ m, dummyT) $ t
fun is_marked m (Const (n, _) $ _) = (n = "_mark_" ^ m)
  | is_marked _ _ = false

fun mark m t = if is_marked m t then t else do_mark m t
fun unmark (Const _ $ t) = t


fun insert_implicit ctxt (ts : term list) =
  let
    fun insert_implicit_term t =
      if is_marked "implicits" t then insert_implicits (unmark t) else t
  in
    map insert_implicit_term ts
  end;


val _ = Context.>>
  (Syntax_Phases.term_check ~11 "implicit_args, mark" (K (map (mark "implicits")))
   #> Syntax_Phases.term_check ~10 "implicit_args, insert phase" insert_implicit
   #> Syntax_Phases.term_check 5 "elaboration" Soft_Type_Inference.elaborate

)
\<close>



lemma "Cons x Nil = ys"
  oops


ML \<open>
\<^term>\<open>Cons x Nil\<close>
\<close>




ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "Nil = B"}
]\<close>

ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "Cons x xs"}
]\<close>


lemma 
  "append (Cons x xs) ys = Cons x (append xs ys)"
  "append Nil ys = ys"
  oops



end