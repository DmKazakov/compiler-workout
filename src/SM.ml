open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

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

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval c p = 
    match p with
        | [] -> c
        | ins :: inss -> match ins with
            | BINOP op -> eval (binop op c) inss
            | CONST n  -> eval (const n c) inss
            | READ     -> eval (read c) inss
            | WRITE    -> eval (write c) inss
            | LD x     -> eval (ld x c) inss
            | ST x     -> eval (st x c) inss

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

let rec compileExpr t =
    match t with
        | Language.Expr.Var x            -> [LD x]
        | Language.Expr.Const n          -> [CONST n]
        | Language.Expr.Binop (op, x, y) -> (compileExpr) x @ (compileExpr y) @ [BINOP op]

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
