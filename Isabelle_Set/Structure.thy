section \<open>Structures\<close>

(*
Title:  structure.thy
Author: Joshua Chen
Date:   Jun 2019

Mathematical structures as set-theoretic functions.
*)

theory Structure
imports Ordinal Function
keywords "struct" :: thy_decl

begin


subsection \<open>Labels for structure fields\<close>

ML \<open>
structure Labels: sig
  val string_to_hash : string -> term
end = struct

val char_hash : term HashArray.hash = HashArray.hash 36

(* Populate char_hash *)
val _ =
let
  (* We hash characters as set-theoretic naturals *)
  fun hash i =
    let val O = @{term "{}"}
    in
      if i = 0 then O
      else @{const "Succ"} $ (hash (i-1))
    end

  fun upd (s, v) = HashArray.update (char_hash, s, v)  (* cf. Pure/General/table.ML *)
in
  upd ("0", hash 0);
  upd ("1", hash 1);
  upd ("2", hash 2);
  upd ("3", hash 3);
  upd ("4", hash 4);
  upd ("5", hash 5);
  upd ("6", hash 6);
  upd ("7", hash 7);
  upd ("8", hash 8);
  upd ("9", hash 9);
  upd ("a", hash 10);
  upd ("b", hash 11);
  upd ("c", hash 12);
  upd ("d", hash 13);
  upd ("e", hash 14);
  upd ("f", hash 15);
  upd ("g", hash 16);
  upd ("h", hash 17);
  upd ("i", hash 18);
  upd ("j", hash 19);
  upd ("k", hash 20);
  upd ("l", hash 21);
  upd ("m", hash 22);
  upd ("n", hash 23);
  upd ("o", hash 24);
  upd ("p", hash 25);
  upd ("q", hash 26);
  upd ("r", hash 27);
  upd ("s", hash 28);
  upd ("t", hash 29);
  upd ("u", hash 30);
  upd ("v", hash 31);
  upd ("w", hash 32);
  upd ("x", hash 33);
  upd ("y", hash 34);
  upd ("z", hash 35)
end

fun get_hash str = HashArray.sub (char_hash, str)

(* Convert strings to ordered tuples of the hashes of each letter. *)
fun string_to_hash str =
  let
    fun mk_pair (t1, t2) = @{const "Pair"} $ t1 $ t2
  in
    String.explode str |>  map (the o get_hash o Char.toString) |> foldr1 mk_pair
  end

end
\<close>


subsection \<open>Notation and syntax\<close>

nonterminal struct_arg and struct_args and struct_sig

syntax
  "_struct_arg"  :: "set \<Rightarrow> (set \<Rightarrow> set type) \<Rightarrow> struct_arg" (infix ":" 45)
  "_struct_args" :: "struct_args \<Rightarrow> struct_arg \<Rightarrow> struct_args" ("(1_ ,/ _)" [40, 41] 40)
  "_struct_sig"  :: "pttrn \<Rightarrow> struct_args \<Rightarrow> set type" ("(; _ . _ ;)")
  "_struct_cond" :: "pttrn \<Rightarrow> struct_args \<Rightarrow> bool \<Rightarrow> set type" ("(; _ . _ where _ ;)")
  "_struct"      :: "set type \<Rightarrow> set type" ("'(;_;')")
  ""             :: "struct_arg \<Rightarrow> struct_args" ("_")
  ""             :: "pttrn \<Rightarrow> struct_args" ("_")

translations
  "(; ty ;)" \<rightharpoonup> "CONST uniq_valued \<cdot> ty"
  "; ref . lbl : typ ;" \<rightharpoonup> "CONST Type (\<lambda>ref. lbl \<in> CONST domain ref \<and> ref`lbl : typ)"
  "; ref . fields, lbl : typ ;" \<rightharpoonup> "; ref . fields ; \<bar> ; ref . lbl : typ ;"
  "; ref . fields where P ;" \<rightharpoonup> "; ref . fields ; \<bar> CONST Type (\<lambda>ref. P)"


text \<open>Structure declaration keyword:\<close>

ML \<open>
Outer_Syntax.local_theory @{command_keyword struct} "Declare structure definitions"
  let
    val parser = Parse.text -- (Parse.$$$ "=" |-- Parse.term)

    fun struct_cmd (name: string, struct_def_str) lthy =
      let
        (* Get the field labels used in the structure declaration.
           Relies on the specific form of the translations defined above! *)
        fun get_labels tm =
          let fun get_labels' tm (lbls as (existing, new)) = case tm of
              @{const elem} $ Free (lbl, _) $ (@{const domain} $ Bound 0) => (existing, lbl :: new)
            | @{const elem} $ Const (lbl, _) $ (@{const domain} $ Bound 0) => (lbl :: existing, new)
            | t1 $ t2 => (
                fst (get_labels' t1 lbls) @ fst (get_labels' t2 lbls), 
                snd (get_labels' t1 lbls) @ snd (get_labels' t2 lbls))
            | Abs (_, _, t) => get_labels' t lbls
            | _ => lbls
          in
            get_labels' tm ([], [])
          end

        val has_dup_labels = has_duplicates (fn tup => (String.compare tup) = EQUAL)

        val struct_def = Syntax.read_term lthy struct_def_str

        val (existing_lbls, new_lbls) = get_labels struct_def

        (* Check for duplicate labels *)
        val _ =
          if has_dup_labels (existing_lbls @ new_lbls)
          then error "Structure type declaration has duplicate labels"
          else ()

        (* Define hashes for new labels *)
        fun define_label lbl = snd o (
          Local_Theory.define (
            (Binding.qualified_name lbl, NoSyn),
            ((Binding.qualified_name (lbl ^ "_lbldef"), []), Labels.string_to_hash lbl)
          ))

        (* Print information *)
        fun print_info name def =
          Output.information ("Structure declaration \"" ^ name ^ "\":\n " ^ def)

        (* Define structure type *)
        fun define_struct_type lthy =
          let val ((Free(name, _), (_, def)), lthy') =
            Local_Theory.define (
              (Binding.qualified_name name, NoSyn),
              ((Binding.qualified_name (name ^ "_typedef"), []),
                Syntax.read_term lthy struct_def_str)
            ) lthy
          in
            print_info name (Syntax.string_of_term lthy' (Thm.prop_of def));
            lthy'
          end

        (* Placeholder: generate typing judgments for the structure fields *)
        fun gen_typings _ = ()

        (* Placeholder: generate definitional axioms as theorems *)
        fun gen_conditions _ = ()
      in
        (new_lbls |> fold (define_label)) lthy |> define_struct_type
          (* |> gen_typings |> gen_conditions *)
      end
  in
    (parser >> (fn (name, def) => fn lthy => struct_cmd (name, def) lthy))
  end
\<close>


text \<open>Structure instance definitions, essentially just syntactic sugar:\<close>

nonterminal instance_arg and instance_args

syntax
  "_instance_arg"  :: "[set, set] \<Rightarrow> instance_arg" (infix ":=" 45)
  "_instance_args" :: "instance_arg \<Rightarrow> instance_args \<Rightarrow> instance_args" ("(1_ ,/ _)" [41, 40] 40)
  "_instance"      :: "instance_args \<Rightarrow> set" ("[;; _ ;;]")
  ""               :: "instance_arg \<Rightarrow> instance_args" ("_")
  ""               :: "pttrn \<Rightarrow> instance_args" ("_")

translations
  "[;; lbl := val ;;]" \<rightharpoonup> "{\<langle>lbl, val\<rangle>}"
  "[;; lbl := val, fields ;;]" \<rightharpoonup> "CONST Cons \<langle>lbl, val\<rangle> [;; fields ;;]"


end
