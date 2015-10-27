(**
 * Cf.
 *     An abstract machine for Lambda-terms normalization
 *     P. Cregut
 *     Proceedings of the 1990 ACM conference on LISP and functional programming  
 *     http://dl.acm.org/citation.cfm?doid=91556.91681&CFID=723138393&CFTOKEN=40299162
 **)

(**
  * make NOGC=y
  * ./kamregions.exe  (for the regions variant)
  * ./kamgc.exe (for the vanilla OCaml variant)
  **)
open Syntax
       
#ifdef CAMLSTACK
let mk_open (n:int) =
  let x = Camlstack.mkref_noscan n in (* basically, a ref is a "one tuple" *)
  let r = Obj.repr x in
  Obj.set_tag r 0;
  Obj.magic x 
let mk_clos (e:env) (t:tm) : closure =  
 let p = Camlstack.mkpair e t in
 let r = Obj.repr p in
 Obj.set_tag r 1;
 Obj.magic p 
let mkpair e t = Camlstack.mkpair e t
let cons e l = Camlstack.cons e l
let push_frame () = Camlstack.push_frame()
let pop_frame () =  Camlstack.pop_frame()
#else
let mk_open (n:int) = Open n
let mk_clos (e:env) (t:tm) : closure = Clos(e,t)  
let mkpair e t = e,t
let cons e l = e::l
let push_frame () = ()
let pop_frame () = ()
#endif

type stack = closure list

let rec norm (env:env) (stack:stack) (tm:tm) (n:int) : tm = match tm with 
  | Abs (t, body) -> 
    begin match stack with 
          | [] ->
             let m = n + 1 in 
	     Abs (norm' env stack t m, norm' (cons (mk_open m) env) stack body m)
          | hd::tl ->
	     norm (cons hd env) tl body n 
    end

  | App(t1, t2) ->
    norm env (cons (mk_clos env t2) stack) t1 n

  | Var x -> 
    let k = find env x in
    begin match k with 
      | Open m -> 
        rebuild env (Var (n - m)) stack n

      | Clos(env', tm) -> 
        norm env' stack tm n
    end

  | Name _ -> rebuild env tm stack n

  | Binder(t1, t2) ->
    let m = n + 1 in
    Binder (norm' env stack t1 n, norm' (cons (mk_open m) env) stack t2 m)

and rebuild env head stack n = match stack with 
  | [] -> head
  | hd::tl -> 
     let arg = match hd with
       | Open m -> Var (n - m)
       | Clos (env, tm) -> norm' env [] tm n in
     rebuild env (App(head, arg)) tl n

and norm' env stack e n = 
  push_frame(); 
  let x = norm env stack e n in
  pop_frame(); 
  x

let norm e = 
  push_frame();
  let x = norm [] [] e 0 in 
  pop_frame(); 
  x

let go fn =
  let input = open_in fn in
  let lexbuf = Lexing.from_channel input in
  let terms =
    try Parser.file Lex.token lexbuf
    with _ ->                     
       begin
        let curr = lexbuf.Lexing.lex_curr_p in
        let line = curr.Lexing.pos_lnum in
        let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
        let tok = Lexing.lexeme lexbuf in
        failwith (Printf.sprintf "Parse error at line %d, col %d, tok %s\n" line cnum tok)
       end in
  let start = Sys.time() in
  let _ = terms |> List.map norm in
  let fin = Sys.time() in
  Printf.printf "Normalization time: %fs\n" (fin -. start)

let _ =
  if Array.length Sys.argv > 1 then go Sys.argv.(1) else go "norm.log"
                                                  
                               
    
(* let rec encode (n:int) =  *)
(*   if n = 0 then z *)
(*   else succ (encode (n - 1)) *)

(* let test2 =  *)
(*   let ten = encode 10 in *)
(*   let hundred = App(App(mul, ten), ten) in  *)
(*   let k = App(App(mul, ten), hundred) in *)
(*   let ten_k = App(App(mul, ten), k) in *)
(*   let _ = norm (minus (minus (minus (minus ten_k k) k) k) k) in  *)
(*   (\*  print_term x; print_string "\n"; *\) *)
(*   Gc.print_stat Pervasives.stdout *)

(* (\*  print_term (norm s) *\) *)
 

  
