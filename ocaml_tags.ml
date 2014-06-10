(* ocaml_tags.ml
 * Matthew Hague (matth1982@gmail.com)
 * Modified by Sosuke Moriguchi (chiguri.s@gmail.com)
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)





open Camlp4.Sig;;

(* identification module *)
module Id = struct
  (*
  (* name is printed with the -loaded-modules switch *)
  let name = "Ocaml global tagger plugin"
  (* cvs id's seem to be the preferred version string *)
  let version = "$Id: ocaml_tags.ml,v 1.6 2009/05/24 21:37:09 matth Exp $"
  *)
  (* name is printed with the -loaded-modules switch *)
  let name = "OCaml global tagger plugin"
  (* cvs id's seem to be the preferred version string *)
  let version = "$Id: ocaml_tags.ml,v 1.8 2014/06/10 07:00:00 chiguri Exp $"
end




(* the real thing containing the real functions *)
module Make (Syntax : Camlp4.Sig.Camlp4Syntax) :
  Camlp4.Sig.Printer(Syntax.Ast).S =
struct
  include Syntax

  (* Because getting filename from Loc seems to corrupt in cases *)
  let orig_filename = ref ""

  let opt_string = function
    | None -> "<None>"
    | Some s -> s


  let get_end_of_path filename = 
    try
        (String.rindex filename '/') + 1
    with Not_found -> 0 
    
  let print_file_tag filename = 
    try
        let ext_pos = String.rindex filename '.' in
        let end_dir_pos = get_end_of_path filename in
        let name_len = (ext_pos - end_dir_pos) in
        let file_name = String.sub filename (end_dir_pos) name_len in 
        let mod_name_first = String.sub filename (end_dir_pos) 1 in
        let mod_name_rest = String.sub filename 
                                       (end_dir_pos + 1) 
                                       (name_len - 1) in
        let mod_name = (String.capitalize mod_name_first) ^ mod_name_rest in
        Printf.printf "%s\t%d\t%s\t%s\n" file_name 0 filename "Module file";
        Printf.printf "%s\t%d\t%s\t%s\n" mod_name 0 filename ("Module " ^ mod_name)
    with _ -> (* oh well, we tried *) ()

  let print_tag (tag, loc, line) = 
    Printf.printf "%s\t%d\t%s\t%s\n" 
                  tag 
                  (Loc.start_line loc) 
                  (*(Loc.file_name loc)*)
                  !orig_filename
                  line


(* for constructor check : if your program is big, gtags will get stuck because of short of memory *)
  let constr_check = false
(* for changing output methodology *)
  let seq i1 i2 = List.append i1 i2
  let nothing = []
  let finalize tags = List.iter print_tag tags
  let put_tag tag loc line = [(tag, loc, line)]
(*
  let seq i1 i2 = ()
  let nothing = ()
  let finalize tags = ()
  let put_tag tag loc line = print_tag (tag, loc, line)
*)

(* Not used : all flags are defined as specific types *)
  let mb_bool mb = 
    match mb with
      Ast.BTrue -> true
    | _ -> false

  let vf_bool = function
  Ast.ViVirtual -> true
    | _ -> false

  let mf_bool = function
  Ast.MuMutable -> true
    | _ -> false

  let pf_bool = function
  Ast.PrPrivate -> true
    | _ -> false

  let of_bool = function
  Ast.OvOverride -> true
    | _ -> false



  let rec ident_tagname ident = 
    match ident with
      (* i . i  (keep last) *)
      Ast.IdAcc(loc, i1, i2) -> ident_tagname i2
      (* i i  (keep first) *)
    | Ast.IdApp(loc, i1, i2) -> ident_tagname i1
      (* foo *)
    | Ast.IdLid(loc, foo) ->  foo
      (* Bar *)
    | Ast.IdUid(loc, bar) -> bar 
      (* $s$ *)
    | Ast.IdAnt(loc, s) -> s


  let rec module_type_info ast = 
    match ast with
      (* functor (s : mt) -> mt *)
    | Ast.MtFun(loc, name, mt1, mt2) -> 
        let info1 = module_type_info mt1 in
        let info2 = module_type_info mt2 in
        seq info1 info2
      (* sig sg end *)
    | Ast.MtSig(loc, sig_item) -> sig_item_info sig_item
    | _ -> nothing

   and ctyp_info ast =
    match ast with
    | Ast.TyCls(loc, i(* #i *) (* #point *)) -> 
        let i_name = ident_tagname i in
        put_tag i_name loc i_name
    | Ast.TyId (loc, i(* i *) (* Lazy.t *)) -> 
        let i_name = ident_tagname i in
        put_tag i_name loc i_name
      (* type t 'a 'b 'c = t constraint t = t constraint t = t *)
    | Ast.TyDcl(loc, s, params, t2, contraint_pairs) ->
        let info1 = put_tag s loc s in
        let info2 = ctyp_info t2 in (* constructors *)
        seq info1 info2
    | Ast.TyAnd(loc, t1, t2(* t and t *)) -> 
        let info1 = ctyp_info t1 in
        let info2 = ctyp_info t2 in
        seq info1 info2
    | Ast.TyOr (loc, t1, t2(* t | t *)) -> 
        let info1 = ctyp_info t1 in
        let info2 = ctyp_info t2 in
        seq info1 info2
    | Ast.TyPrv(loc, t(* private t *)) -> (ctyp_info t) 
    | Ast.TyMut(loc, t (* mutable t *)) -> (ctyp_info t)
      (* for constructors *)
    | Ast.TyOf(loc, t1, t2) when constr_check -> (ctyp_info t1)
    | Ast.TySum(loc, t (* top of constructors *)) when constr_check -> (ctyp_info t)
    | _ -> nothing

  and module_binding_info ast =
    match ast with
      (* mb and mb *) (* module rec (s : mt) = me and (s : mt) = me *)
      Ast.MbAnd(loc, mb1, mb2) -> 
        let info1 = module_binding_info mb1 in
        let info2 = module_binding_info mb2 in
        seq info1 info2
      (* s : mt = me *)
    | Ast.MbColEq (loc, s, mt, me) -> 
        let info1 = put_tag s loc s in
        let info2 = module_expr_info me in
        seq info1 info2
      (* s : mt *)
    | Ast.MbCol (loc, s, mt) -> put_tag s loc s
    | _ -> nothing


  and rec_binding_info ast =
    match ast with
      (* rb ; rb *)
    | Ast.RbSem(loc, rb1, rb2) -> 
        let info1 = rec_binding_info rb1 in
        let info2 = rec_binding_info rb2 in
        seq info1 info2
      (* i = e *)
    | Ast.RbEq (loc, i, e) -> 
        let i_name = ident_tagname i in
        put_tag i_name loc i_name
    | _ -> nothing

  and patt_info ast =
    match ast with
      Ast.PaId (loc, i(* i *)) ->
        let i_tag = ident_tagname i in
        put_tag i_tag loc i_tag
    | Ast.PaAli(loc, p1, p2 (* p as p *) (* (Node x y as n) *)) -> (patt_info p2)
    | Ast.PaAnt(loc, s (* $s$ *)) ->  put_tag s loc ("$" ^ s ^ "$")
    | Ast.PaCom(loc, p1, p2(* p, p *)) -> 
        let info1 = patt_info p1 in
        let info2 = patt_info p2 in
        seq info1 info2
    | Ast.PaEq (loc, i, p(* i = p *)) -> 
        let i_name = ident_tagname i in
        let info1 =  put_tag i_name loc i_name in
        let info2 = patt_info p in
        seq info1 info2
    | Ast.PaStr(loc, s(* s *)) -> put_tag s loc s
    | Ast.PaTup(loc, p(* ( p ) *)) -> patt_info p
    | Ast.PaTyc(loc, p, t(* (p : t) *)) -> patt_info p
    | Ast.PaTyp(loc, i (* #i *)) -> 
        let i_name = ident_tagname i in
        put_tag i_name loc ("#" ^ i_name)
    | _ -> nothing
    
  and sig_item_info ast = 
    match ast with
      (* class cict *)
    | Ast.SgCls(loc, cict) -> (class_type_info cict)
      (* class type cict *)
    | Ast.SgClt(loc, cict) -> (class_type_info cict)
      (* sg ; sg *)
    | Ast.SgSem(loc, sg1, sg2) ->
        let info1 = sig_item_info sg1 in
        let info2 = sig_item_info sg2 in
        seq info1 info2
      (* exception t *)
    | Ast.SgExc(loc, t) -> (ctyp_info t)
      (* module s : mt *)
    | Ast.SgMod(loc, s, mt) -> 
        let info1 = put_tag s loc ("module " ^ s) in
        let info2 = module_type_info mt in
        seq info1 info2
      (* module rec mb *)
    | Ast.SgRecMod(loc, mb) -> (module_binding_info mb)
      (* module type s = mt *)
    | Ast.SgMty(loc, s, mt) -> 
        let info1 = put_tag s loc ("module type" ^ s) in
        let info2 = module_type_info mt in
        seq info1 info2
      (* value s : t *)
    | Ast.SgVal(loc, s, t) -> put_tag s loc ("value " ^ s)
      (* type t *)
    | Ast.SgTyp(loc, t) -> (ctyp_info t)
    | _ -> nothing

  and module_expr_info ast = 
    match ast with
      (* me me *)
      Ast.MeApp(loc, me1, me2) -> 
        let info1 = module_expr_info me1 in
        let info2 = module_expr_info me2 in
        seq info1 info2
      (* functor (s : mt) -> me *)
    | Ast.MeFun(loc, s, mt, me) -> (module_expr_info me)
      (* struct st end *)
    | Ast.MeStr(loc, st) -> (str_item_info st)
      (* (me : mt) *)
    | Ast.MeTyc(loc, me, mt) -> 
        let info1 = module_expr_info me in
        let info2 = module_type_info mt in
        seq info1 info2
    | _ -> nothing

  and binding_info ast =
    match ast with
      Ast.BiNil(loc) -> nothing
      (* bi and bi *) (* let a = 42 and c = 43 *)
    | Ast.BiAnd(loc, bi1, bi2) ->
        let info1 = binding_info bi1 in
        let info2 = binding_info bi2 in
        seq info1 info2
      (* p = e *) (* let patt = expr *)
    | Ast.BiEq (loc, p, e) -> patt_info p 
      (* $s$ *)
    | Ast.BiAnt(loc, s) -> put_tag s loc ("$" ^ s ^ "$")


  and class_type_info ast =
    match ast with
      (* (virtual)? i ([ t ])? *)
    | Ast.CtCon(loc, mb, i, t) -> 
        let line = if (vf_bool mb) then "class virtual " else "class " in
        let i_name = ident_tagname i in
        put_tag i_name loc (line ^ i_name)
      (* [t] -> ct *)
    | Ast.CtFun(loc, t, ct) -> class_type_info ct
      (* object ((t))? (csg)? end *)
    | Ast.CtSig(loc, t, csg) -> class_sig_item_info csg
      (* ct and ct *)
    | Ast.CtAnd(loc, ct1, ct2) -> 
        let info1 = class_type_info ct1 in
        let info2 = class_type_info ct2 in
        seq info1 info2
      (* ct : ct *)
    | Ast.CtCol(loc, ct1, ct2) -> 
        let info1 = class_type_info ct1 in
        let info2 = class_type_info ct2 in
        seq info1 info2
      (* ct = ct *)
    | Ast.CtEq (loc, ct1, ct2) -> class_type_info ct1
    | _ -> nothing
  and class_sig_item_info ast =
    match ast with
      (* csg ; csg *)
    | Ast.CgSem(loc, csg1, csg2) -> 
        let info1 = class_sig_item_info csg1 in
        let info2 = class_sig_item_info csg2 in
        seq info1 info2
      (* method (private)? s : t *)
    | Ast.CgMth(loc, s, mb, t) -> 
        let line = if (pf_bool mb) then "method private " else "method " in
        put_tag s loc (line ^ s)
      (* val (mutable)? (virtual)? s : t *)
    | Ast.CgVal(loc, s, mb1, mb2, t) -> 
        let line1 = if (mf_bool mb1) then "val mutable " else "val " in
        let line2 = if (vf_bool mb2) then "virtual " else "" in
        put_tag s loc (line1 ^ line2 ^ s)
      (* method (private)? virtual s : t *)
    | Ast.CgVir(loc, s, mb, t) -> 
        let line = if (pf_bool mb) then "method private " else "method " in
        put_tag s loc (line ^ s)
    | _ -> nothing
  and class_str_item_info ast =
    match ast with
      (* cst ; cst *)
      Ast.CrSem(loc, cst1, cst2) -> 
        let info1 = class_str_item_info cst1 in
        let info2 = class_str_item_info cst2 in
        seq info1 info2
      (* method (private)? s : t = e or method (private)? s = e *)
    | Ast.CrMth(loc, s, mb1, mb2, e, t) -> 
        let line1 = if (of_bool mb1) then "override " else "" in
        let line2 = if (pf_bool mb2) then "method private " else "method " in
        put_tag s loc (line1 ^ line2 ^ s)
      (* value (mutable)? s = e *)
    | Ast.CrVal(loc, s, mb1, mb2, e) -> 
        let line1 = if (of_bool mb1) then "override " else "" in
        let line2 = if (mf_bool mb2) then "val mutable " else "val " in
        put_tag s loc (line1 ^ line2 ^ s)
      (* method virtual (private)? s : t *)
    | Ast.CrVir(loc, s, mb, t) -> 
        let line = if (pf_bool mb) then "method virtual private " else "method virtual " in
        put_tag s loc (line ^ s)
      (* value (mutable)? virtual s : t *)
    | Ast.CrVvr(loc, s, mb, t) -> 
        let line = if (mf_bool mb) then "val mutual virtual " else "val virtual " in
        put_tag s loc (line ^ s)
    | _ -> nothing

  and class_expr_info ast =
    match ast with
      (* ce e *)
      Ast.CeApp(loc, ce, e) -> class_expr_info ce 
      (* (virtual)? i ([ t ])? *)
    | Ast.CeCon(loc, mb, i, t) -> 
        let tag_name = ident_tagname i in
        let line = if (vf_bool mb) then "class virtual " else "class " in
        put_tag tag_name loc (line ^ tag_name)
      (* fun p -> ce *)
    | Ast.CeFun(loc, p, ce) -> (class_expr_info ce)
      (* let (rec)? bi in ce *)
    | Ast.CeLet(loc, mb, bi, ce) -> 
        let info1 = binding_info bi in
        let info2 = class_expr_info ce in
        seq info1 info2
      (* object ((p))? (cst)? end *)
    | Ast.CeStr(loc, p, cst) -> class_str_item_info cst
      (* ce : ct *)
    | Ast.CeTyc(loc, ce, ct) -> 
        let info1 = class_expr_info ce in
        let info2 = class_type_info ct in
        seq info1 info2
      (* ce and ce *)
    | Ast.CeAnd(loc, ce1, ce2) -> 
        let info1 = class_expr_info ce1 in
        let info2 = class_expr_info ce2 in
        seq info1 info2
      (* ce = ce *)
    | Ast.CeEq (loc, ce1, ce2) -> 
        let info1 = class_expr_info ce1 in
        let info2 = class_expr_info ce2 in
        seq info1 info2
    | _ -> nothing
    
  and str_item_info ast = 
    match ast with
      (* class cice *)
      Ast.StCls(loc, cice) -> class_expr_info cice
      (* class type cict *)
    | Ast.StClt(loc, cict) -> class_type_info cict
      (* st ; st *)
    | Ast.StSem(loc, st1, st2) -> 
        let info1 = str_item_info st1 in
        let info2 = str_item_info st2 in
        seq info1 info2
      (* exception t or exception t = i *)
    | Ast.StExc(loc, t, i) -> (ctyp_info t)
      (* e *)
    | Ast.StExp(loc, e) -> nothing
      (* module s = me *)
    | Ast.StMod(loc, s, me) -> 
        let info1 = put_tag s loc ("module " ^ s) in
        let info2 = module_expr_info me in
        seq info1 info2
      (* module rec mb *)
    | Ast.StRecMod(loc, mb) -> (module_binding_info mb)
      (* module type s = mt *)
    | Ast.StMty(loc, s, mt) -> 
        let info1 = put_tag s loc ("module " ^ s) in
        let info2 = module_type_info mt in
        seq info1 info2
      (* value (rec)? bi *)
    | Ast.StVal(loc, mb, bi) -> (binding_info bi)
      (* type t *)
    | Ast.StTyp(loc, t) -> (ctyp_info t)
    | _ -> nothing

  (* print_interf shall be called on .mli files *)
  let print_interf ?input_file ?output_file ast =
    orig_filename := opt_string input_file;
    print_file_tag (opt_string input_file);
    let tags = sig_item_info ast in
    finalize tags


  (* print_implem shall be called on .ml files *)
  let print_implem ?input_file ?output_file ast =
    orig_filename := opt_string input_file;
    print_file_tag (opt_string input_file);
    let tags = str_item_info ast in
    finalize tags

      
end

(* apply everything to register the new printer *)
module M = Camlp4.Register.OCamlPrinter(Id)(Make)

(* end of source *)

