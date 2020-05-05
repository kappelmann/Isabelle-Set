section \<open>Objects\<close>

text \<open>
  "Objects" are the abstraction of records/structures/mathematical objects.
  Their underlying implementation is as set-theoretic functions.
\<close>

theory Object_Old
imports Function String

keywords "object" :: thy_decl

begin

subsection \<open>Syntax: object schema declarations\<close>

definition selector :: "[set, set] \<Rightarrow> set" ("(_)[(_)]" [1000, 0] 1000)
  where "object[lbl] \<equiv> object `lbl"

definition composer :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  where "composer lbl pred \<equiv> (\<lambda>x. pred x[lbl] x)"

nonterminal object_arg and object_args
syntax
  "_object_arg"   :: "id \<Rightarrow> set \<Rightarrow> object_arg" ("'(_ _')")
  "_object_args"  :: "object_args \<Rightarrow> object_arg \<Rightarrow> object_args" ("_ _" [40, 41] 40)
  "_object_comp"  :: "object_args \<Rightarrow> logic \<Rightarrow> set type" ("\<lparr> _./ _ \<rparr>")
  "_object_comp2" :: "object_args \<Rightarrow> logic \<Rightarrow> set type"
  ""              :: "object_arg \<Rightarrow> object_args" ("_")
translations
  "_object_comp args P" \<rightleftharpoons> "_object_comp2 args (CONST K P)"
  "_object_comp2 (_object_args args (_object_arg a A)) P" \<rightleftharpoons>
    "_object_comp2 args (CONST composer A (\<lambda>a. P))"
  "_object_comp2 (_object_arg a A) P" \<rightleftharpoons> "CONST type (CONST composer A (\<lambda>a. P))"

ML \<open>
Outer_Syntax.local_theory \<^command_keyword>\<open>object\<close> "object declarations"
  let
    val parser =
      Parse.name
      -- Scan.option (Scan.repeat Parse.term)
      -- (\<^keyword>\<open>is\<close> |-- Parse.term)

    fun object_cmd (name, params, object_defstr) lthy =
      (let
        (*
          Get the field labels used in the declaration.
          This relies on the specific form of the translations defined above!
        *)
        fun get_labels (\<^const>\<open>composer\<close> $ A $ Abs (_, _, t)) = A :: get_labels t
          | get_labels (Const (\<^const_name>\<open>type\<close>, _) $ t) = get_labels t
          | get_labels (Const (\<^const_name>\<open>Int_type\<close>, _) $ _ $ t) = get_labels t
          | get_labels _ = []

        val object_def = Syntax.read_term lthy object_defstr
        val labels = get_labels object_def

        (* val string_labels =
          labels |> filter (fn t => case t of \<^const>\<open>string\<close> $ _ => true | _ => false) *)

        val _ =
          (* if length labels > length string_labels
          then error "Label error"
          else *)
          if has_duplicates (op =) labels (* string_labels *)
          then error "Object declaration has duplicate labels"
          else ()

        (* fun define_label_const tm = fn lthy =>
          let val (name, typ) = dest_Free tm
          in
            (* FIXME proper Local_Theory.declaration instead of Local_Theory.background_theory *)
            lthy |> Local_Theory.background_theory (
              snd o Sign.declare_const lthy ((Binding.qualified_name name, typ), NoSyn)) 
          end *)

        fun print_info def =
          Output.writeln ("object\n  " ^ def)

        fun define_object_type lthy =
          let
            val def_tm =
              let val body = Syntax.read_term lthy object_defstr
              in
                case params of
                  SOME [] => body
                | SOME args => foldl1
                    (op o)
                    (map (Term.absfree o dest_Free o Syntax.read_term lthy) args)
                    body
                | NONE => body
              end

            val ((tm, (_, def_th)), lthy') =
              Local_Theory.define (
                (Binding.qualified_name name, NoSyn),
                ((Binding.qualified_name (name ^ "_def"), []), def_tm)
              ) lthy
          in
            print_info (Syntax.string_of_term lthy' (Thm.prop_of def_th));
            lthy'
          end

        (* Placeholder: generate typing judgments for the object fields *)
        fun gen_typings _ = ()

        (* Placeholder: generate definitional axioms as theorems *)
        fun gen_conditions _ = ()
      in
        lthy
        (* |> fold define_label_const new_labels *)
        |> define_object_type
        (* |> gen_typings |> gen_conditions *)
      end)
  in
    parser >> (fn ((name, params), def) => object_cmd (name, params, def))
  end
\<close>


subsection \<open>Syntax: object instance definitions\<close>

nonterminal instance_arg and instance_args
syntax
  "_instance_arg"  :: "[set, set] \<Rightarrow> instance_arg" (infix "=" 45)
  "_instance_args" :: "instance_arg \<Rightarrow> instance_args \<Rightarrow> instance_args" ("(1_ ,/ _)" [41, 40] 40)
  "_instance"      :: "instance_args \<Rightarrow> set" ("\<lparr> _ \<rparr>")
  ""               :: "instance_arg \<Rightarrow> instance_args" ("_")
  ""               :: "pttrn \<Rightarrow> instance_args" ("_")
translations
  "\<lparr> lbl = val \<rparr>" \<rightharpoonup> "{\<langle>lbl, val\<rangle>}"
  "\<lparr> lbl = val, fields \<rparr>" \<rightharpoonup> "CONST cons \<langle>lbl, val\<rangle> \<lparr> fields \<rparr>"


subsection \<open>Rules\<close>

lemma object_iffs [simp]:
  "M: type (composer A P) \<longleftrightarrow> M: type (P (M[A]))"
  "M: type (K Q) \<longleftrightarrow> Q"
  by unfold_types (auto simp: selector_def composer_def)

lemmas object_simps =
  selector_def
  composer_def
  apply_singleton [unfolded selector_def[symmetric]]
  apply_pair1 [unfolded selector_def[symmetric]]
  apply_pair2 [unfolded selector_def[symmetric]]

subsection \<open>Rudimentary automation\<close>

method eval_selector = (
  (unfold selector_def)?,
  (subst function_apply; auto?), (rule cons_functionI)+,
  (auto; string_neq)+
)+


end
