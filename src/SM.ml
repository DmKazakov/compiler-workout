open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config


let binop op (w, y :: x :: st, c) = (w, ((Language.Expr.to_func op) x y) :: st, c)

let const n (w, st, c) = (w, n :: st, c)

let read (w, st, (s, x :: i, o)) = (w, x :: st, (s, i, o))

let write (w, x :: st, (s, i, o)) = (w, st, (s, i, o @ [x]))

let ld x (w, st, (s, i, o)) = (w, (Language.State.eval s x) :: st, (s, i, o))

let st x (w, z :: st, (s, i, o)) = (w, st, (Language.State.update x z s, i, o))

let rec init args c = match args with
    | [] -> c
    | arg :: args -> init args (st arg c)

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)

  let rec eval e c p = 
    match p with
        | [] -> c
        | ins :: inss -> match ins with
            | BINOP op    -> eval e (binop op c) inss
            | CONST n     -> eval e (const n c) inss
            | READ        -> eval e (read c) inss
            | WRITE       -> eval e (write c) inss
            | LD x        -> eval e (ld x c) inss
            | ST x        -> eval e (st x c) inss
            | LABEL _     -> eval e c inss
            | JMP l       -> eval e c (e#labeled l)
            | BEGIN (args, locs) -> let (w, z, (c, i, o)) = c in
                                    let c = State.enter c (args @ locs) in
                                    eval e (init args (w, z, (c, i, o))) inss
            | END         -> (match c with
                                | ([], _, _) -> c
                                | ((p, c') :: w, z, (c, i, o)) -> eval e (w, z, (State.leave c c', i, o)) p)
            | CALL f      -> let (w, z, (c, i, o)) = c in
                             eval e ((inss, c) :: w, z, (c, i, o)) (e#labeled f)
            | CJMP (m, l) -> match c with
                                | (w, z :: st, c) -> if ((m = "z") && (z = 0)) || ((m = "nz") && (z <> 0)) then (eval e (w, st, c) (e#labeled l)) else (eval e (w, st, c) inss)

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [], None)) p in o

let to_label n = Printf.sprintf ("L%d") n

let rec compile' n =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (f, l)      -> let res, m = compile' n (Stmt.Call(f, l)) in
                             res
  in
  let rec exprs inss = match inss with
    | []   -> []
    | (ins :: inss) -> (exprs inss) @ (expr ins)
  in
  function
  | Stmt.Seq (s1, s2)   -> let l1, m = compile' n s1 in 
                           let l2, k = compile' m s2 in
                               l1 @ l2, k
  | Stmt.Read x         -> [READ; ST x], n
  | Stmt.Write e        -> expr e @ [WRITE], n
  | Stmt.Assign (x, e)  -> expr e @ [ST x], n
  | Stmt.Skip           -> [], n
  | Stmt.If (e, s1, s2) -> let cond = expr e in
                           let then_b, m = compile' (n + 1) s1 in
                           let else_b, k = compile' (m + 1) s2 in
                           cond @ [CJMP ("z", (to_label n))] @ then_b @ [JMP (to_label m)] @ [LABEL (to_label n)] @ else_b @ [JMP (to_label m)] @ [LABEL (to_label m)], k
  | Stmt.While (e, s1)  -> let cond = expr e in
                           let loop, m = compile' (n + 2) s1 in
                           [LABEL (to_label n)] @ cond @ [CJMP ("z", (to_label (n + 1)))] @ loop @ [JMP (to_label n)] @ [LABEL (to_label (n + 1))], m
  | Stmt.Repeat (s1, e)   -> let body, m = compile' (n + 1) s1 in
                           [LABEL (to_label n)] @ body @ (expr e) @ [CJMP ("z", (to_label n))], m
  | Stmt.Call (f, l)     -> exprs l @ [CALL f], n
  | Stmt.Return None     -> [END], n
  | Stmt.Return (Some e) -> (expr e) @ [END], n

let rec compileDef n = function
    | []                           -> [], n
    | (f, (args, locs, body)) :: l -> let cbody, n = compile' n body in
                                      let left, n  = compileDef n l in
                                      [LABEL f; BEGIN (args, locs)] @ cbody @ [END] @ left, n

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = let defs, n = compileDef 0 defs in
                        let stm, n = compile' n p in
                        stm @ [END] @ defs
