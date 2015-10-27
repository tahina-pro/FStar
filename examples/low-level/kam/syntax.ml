type tm =
  | Var of int          (* de Bruijn *)
  | Name of string
  | Abs of tm * tm
  | App of tm  * tm 
  | Binder of tm * tm
                     
type env = closure list

and closure = 
  | Open of int
  | Clos of env * tm
                    
let rec close x ix body = match body with 
  | Var _ -> body
  | Name y -> if y=x then Var ix else body
  | App(t1, t2) -> App(close x ix t1, close x ix t2)
  | Abs (t1, t2) -> Abs (close x ix t1, close x (ix + 1) t2)
  | Binder (t1, t2) -> Binder (close x ix t1, close x (ix + 1) t2)
let abs' (x, t1, body) = Abs(t1, close x 0 body)
let abs (x, body) = abs' (x, Name "_", body)

let x = "0"
let y = "1"
let f = "2"
let g = "3"
let n = "4"
let h = "5"
let m = "6"
let z = abs(f, abs(x, Name x))
let one = abs(f, abs(x, App(Name f, Name x)))
let succ n = abs(f, abs(x, App(Name f, App(App(n, Name f), Name x))))
let pred = abs(n, abs(f, abs(x, App(App(App(Name n, (abs(g, abs(h, App(Name h, App(Name g, Name f)))))), abs(y, Name x)), abs(y, Name y)))))
let minus m n = App(App(n, pred), m)
let mul = abs(m, abs(n, abs(f, App(Name m, (App(Name n, Name f))))))
             
let push m = 
  let next_char = fst m + 1 in
  let x = Char.chr next_char in
  x, (next_char, x::snd m)

let rec term_to_string_raw = function 
  | Var x -> string_of_int x
  | Name x -> Printf.sprintf "(Name %s)" x
  | Abs (t1, t2) -> Printf.sprintf  "(Abs %s %s)" (term_to_string_raw t1) (term_to_string_raw t2)
  | App(t1, t2) -> Printf.sprintf "(App %s %s)" (term_to_string_raw t1) (term_to_string_raw t2)
  | Binder(t1, t2) -> Printf.sprintf "(Binder %s %s)" (term_to_string_raw t1) (term_to_string_raw t2)

let rec clos_to_string = function 
  | Open m -> Printf.sprintf "(Open %d)" m
  | Clos(env, x) -> Printf.sprintf "(Clos %s %s)" (env_to_string env) (term_to_string_raw x)

and env_to_string env = 
  let s = List.map clos_to_string env in 
  Printf.sprintf "[%s]" (String.concat "; " s)

let print_term_raw t = print_string (term_to_string_raw t)

let rec find env x = match env with 
  | k::tl -> 
    if x=0 then k else find tl (x - 1)
  | [] -> raise Not_found

let rec print_term m = function 
  | Var x -> print_char (find (snd m) x)
  | Name x -> print_string "(Name "; print_string x; print_string ")"
  | Abs (t1, t2) -> let x, m' = push m in print_string "(Abs ("; print_char x; print_string ":"; print_term m t1; print_string "). "; print_term m' t2; print_string ")"
  | Binder (t1, t2) -> let x, m' = push m in print_string "(Binder ("; print_char x; print_string ":"; print_term m t1; print_string "). "; print_term m' t2; print_string ")"
  | App(t1, t2) -> print_string "("; print_term m t1; print_string " "; print_term m t2; print_string ")"

let print_term x = print_term (Char.code 'a' - 1, []) x; print_string "\n"
