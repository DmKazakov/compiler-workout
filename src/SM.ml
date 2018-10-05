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
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

let binop op (y :: x :: st, c) = ((Language.Expr.applyOp op x y) :: st, c)

let const n (st, c) = (n :: st, c)

let read (st, (s, x :: i, o)) = (x :: st, (s, i, o))

let write (x :: st, (s, i, o)) = (st, (s, i, o @ [x]))

let ld x (st, (s, i, o)) = ((s x) :: st, (s, i, o))

let st x (z :: st, (s, i, o)) = (st, (Language.Expr.update x z s, i, o))

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
            | CJMP (m, l) -> match c with
                              | (z :: st, c) -> if ((m = "z") && (z = 0)) || ((m = "nz") && (z <> 0)) then (eval e (st, c) (e#labeled l)) else (eval e (st, c) inss)

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let to_label n = Printf.sprintf ("L%d") n

let rec compile' n =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
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
  | Stmt.Until (s1, e)   -> let body, m = compile' (n + 1) s1 in
                           [LABEL (to_label n)] @ body @ (expr e) @ [CJMP ("z", (to_label n))], m

let compile x = let res, _ = compile' 0 x in res
