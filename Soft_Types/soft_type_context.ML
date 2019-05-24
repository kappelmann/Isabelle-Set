(*  Title:      soft_type_context.ML
    Author:     Alexander Krauss

Context information regarding soft types.

Allows the declaration of soft types for symbols, which are then available for type checking.
Symbols are either free variables (declared in the context) or constants.

*)

structure Soft_Type_Context =
struct

  (* Context data. Maps terms to soft types. *)
  structure Ctxt = Generic_Data(
    type T = thm Termtab.table * thm Symtab.table;
    val empty = (Termtab.empty, Symtab.empty);
    val extend = I;
    fun merge ((a1, b1), (a2, b2)) =
        (Termtab.merge Thm.eq_thm_prop (a1, a2), 
         Symtab.merge Thm.eq_thm_prop (b1, b2));
  );

  fun put_sty (Const (n, _)) sty = apsnd (Symtab.update (n, sty))
    | put_sty t sty = apfst (Termtab.update (t, sty))

  fun get_sty tabs (Const (n, _)) = Symtab.lookup (snd tabs) n
    | get_sty tabs t = Termtab.lookup (fst tabs) t

  (* Canonical get and put operations *)
  fun put t sty = Ctxt.map (put_sty t sty);
  fun get ctxt t = get_sty (Ctxt.get ctxt) t;

  (* Breaks a typing judgment into its term and type parts.
     Accepts both pure judgement form or embedded into HOL.Trueprop.
   *)
  fun dest_typing tm =
      case tm of
        Const (@{const_name has_type}, _) $ t $ T => (t, T)
      | Const ("HOL.Trueprop", _) $ (Const (@{const_name has_type}, _) $ t $ T) => (t, T)
      | _ => Exn.error ("dest_typing: not a typing judgment" ^ \<^make_string> tm)


  fun add_typing thm ctxt =
    let val (x, _) = dest_typing (Thm.prop_of thm)
    in put x thm ctxt
    end;

  val _ = Theory.setup (Attrib.setup @{binding type}
    (Scan.succeed (Thm.declaration_attribute add_typing)) "Declare a soft type")


end
