section \<open>Objects\<close>

text \<open>
  "Objects" are the abstraction of records/structures/mathematical objects.
  Their underlying implementation is as set-theoretic functions.
\<close>

theory Object
imports Function String

keywords "object" :: thy_decl

begin

subsection \<open>Syntax setup\<close>

definition selector :: "[set, set] \<Rightarrow> set" ("(_)[(_)]" [901, 0] 900)
  where "object[lbl] \<equiv> object`lbl"

definition comp :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  where [squash]: "comp lbl pred \<equiv> (\<lambda>x. pred (x[lbl]) x)"

nonterminal object_arg and object_args
syntax
  "_object_arg"   :: "set \<Rightarrow> id \<Rightarrow> object_arg" ("'(_ _')")
  "_object_args"  :: "object_args \<Rightarrow> object_arg \<Rightarrow> object_args" ("_ _" [40, 41] 40)
  "_object_comp"  :: "object_args \<Rightarrow> logic \<Rightarrow> set type" ("\<lparr> _. _ \<rparr>")
  "_object_comp2" :: "object_args \<Rightarrow> logic \<Rightarrow> set type"
  ""              :: "object_arg \<Rightarrow> object_args" ("_")
translations
  "_object_comp args P" \<rightleftharpoons> "_object_comp2 args (CONST K P)"
  "_object_comp2 (_object_args args (_object_arg A a)) P" \<rightleftharpoons>
    "_object_comp2 args (CONST comp A (\<lambda>a. P))"
  "_object_comp2 (_object_arg A a) P" \<rightleftharpoons> "CONST Type (CONST comp A (\<lambda>a. P))"

ML \<open>
Outer_Syntax.local_theory \<^command_keyword>\<open>object\<close> "Object declarations"
  let
    val parser =
      Parse.name
      -- Scan.option (Scan.repeat Parse.term)
      -- (Parse.$$$ "is" |-- Parse.term)

    fun object_cmd (name: string, params, object_defstr) lthy =
      let
        (*
          Get the field labels used in the declaration.
          This relies on the specific form of the translations defined above!
        *)
        fun get_labels (\<^const>\<open>comp\<close> $ A $ Abs (_, _, t)) = A :: get_labels t
          | get_labels (Const (\<^const_name>\<open>Type\<close>, _) $ t) = get_labels t
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

        fun print_info name def =
          Output.information ("Object declaration \"" ^ name ^ "\":\n " ^ def)

        fun define_object_type lthy =
          let
            val def_tm =
              let val body = Syntax.read_term lthy object_defstr
              in
                case params of
                  SOME [] => body
                | SOME args =>
                    foldl1
                      (op o)
                      (map (Term.absfree o dest_Free o Syntax.read_term lthy) args)
                      body
                | NONE => body
              end

            val ((Free(name, _), (_, def)), lthy') =
              Local_Theory.define (
                (Binding.qualified_name name, NoSyn),
                ((Binding.qualified_name (name ^ "_typedef"), []), def_tm)
              ) lthy
          in
            print_info name (Syntax.string_of_term lthy' (Thm.prop_of def));
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
      end
  in
    (parser >> (fn ((name, params), def) => fn lthy =>
      object_cmd (name, params, def) lthy))
  end
\<close>

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
  "M : Type (comp A P) \<longleftrightarrow> M : Type (P (M[A]))"
  "M : Type (K Q) \<longleftrightarrow> Q"
  by squash_types

lemmas object_simps [unfolded selector_def[symmetric], simp] =
  apply_singleton
  apply_pair1
  apply_pair2


end
