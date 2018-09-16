(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open Ostap

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

        (* val evalOp : string -> int -> int *)                    
    let applyOp op n m = 
      match op with
        | "+"  -> n + m
        | "-"  -> n - m
        | "*"  -> n * m
        | "/"  -> n / m
        | "%"  -> n mod m
        | "<"  -> if n <  m then 1 else 0
        | "<=" -> if n <= m then 1 else 0
        | ">"  -> if n >  m then 1 else 0
        | ">=" -> if n >= m then 1 else 0
        | "==" -> if n =  m then 1 else 0
        | "!=" -> if n <> m then 1 else 0
        | "&&" -> if (n = 0) || (m = 0) then 0 else 1
        | "!!" -> if (n = 0) && (m = 0) then 0 else 1

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval s e = 
      match e with
        | Var x            -> s x
        | Const n          -> n
        | Binop (op, x, y) -> applyOp op (eval s x) (eval s y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      expr:
        !(Util.expr
           (fun x -> x)
           [|
             `Lefta , [ostap ("!!" ), (fun x y -> Binop ("!!", x, y))];
             `Lefta , [ostap ("&&" ), (fun x y -> Binop ("&&", x, y))];
             `Nona  , [ostap ("=="), (fun x y -> Binop ("==", x, y)); ostap ("<="), (fun x y -> Binop ("<=", x, y)); 
                ostap ("<"), (fun x y -> Binop ("<", x, y)); ostap (">="), (fun x y -> Binop (">=", x, y)); 
                ostap (">"), (fun x y -> Binop (">", x, y)); ostap ("!="), (fun x y -> Binop ("!=", x, y))];
             `Lefta , [ostap ("+" ), (fun x y -> Binop ("+", x, y)); ostap ("-"), (fun x y -> Binop ("-", x, y))];
             `Lefta , [ostap ("*" ), (fun x y -> Binop ("*", x, y)); ostap ("/"), (fun x y -> Binop ("/", x, y)); 
                ostap ("%"), (fun x y -> Binop ("%", x, y))]
           |]
           primary
         );
      
      primary: x:IDENT {Var x} | n:DECIMAL {Const n} | -"(" expr -")"
    )

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    let read x (s, (n :: i), o) = ((Expr.update x n s), i, o)

    let write x (s, i, o) = (s, i, o @ [Expr.eval s x])

    let assign x e (s, i, o) = (Expr.update x (Expr.eval s e) s, i, o)

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval c t = 
      match t with
        | Read x        -> read x c 
        | Write x       -> write x c
        | Assign (x, e) -> assign x e c
        | Seq (t1, t2)  -> eval (eval c t1) t2

    (* Statement parser *)
    ostap (
      simple_stmt:
        x:IDENT ":=" c:!(Expr.expr) {Assign (x, c)}
      | "read" "(" x:IDENT ")"         {Read x}
      | "write" "(" c:!(Expr.expr) ")" {Write c};

      parse: <s::ss> : !(Util.listBy)[ostap (";")][simple_stmt] {List.fold_left (fun s ss -> Seq (s, ss)) s ss}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
