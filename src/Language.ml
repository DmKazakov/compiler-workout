(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _ -> failwith (Printf.sprintf "Unknown binary operator %s" op) 

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                              
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                    
    let rec eval env (st, i, o, r) expr = 
        match expr with
        | Const n          -> (st, i, o, Some n)
        | Var x            -> (st, i, o, Some (State.eval st x))
        | Binop (op, x, y) -> let (st1, i1, o1, Some r1) = eval env (st, i, o, r) x in
                              let (st2, i2, o2, Some r2) = eval env (st1, i1, o1, Some r1) y in
                              (st2, i2, o2, Some (to_func op r1 r2))
        | Call (fname, argExprs) ->
            let evalArg argExpr (conf', argVals) =
                let conf', argVal = evalChecked env conf' argExpr in
                conf', argVal::argVals
            in
            let conf', argVals = List.fold_right evalArg argExprs ((st, i, o, r), []) in
            env#definition env fname argVals conf'
            and evalChecked env conf expr =
            let (st, i, o, ret) = eval env conf expr in
            match ret with | Some x -> (st, i, o, None), x | None -> failwith "Internal error"
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse:
      !(Ostap.Util.expr 
             (fun x -> x)
         (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
        `Lefta, ["!!"];
        `Lefta, ["&&"];
        `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
        `Lefta, ["+" ; "-"];
        `Lefta, ["*" ; "/"; "%"];
              |] 
         )
         primary);
      
      primary:
        x:DECIMAL {Const x} |
        fname:IDENT -"(" argExprs:!(Ostap.Util.list0)[parse] -")" { Call (fname, argExprs) } |
        var:IDENT {Var var} |
        -"(" parse -")"
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
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    let read x (st, (n :: i), o, _) = ((State.update x n st), i, o, None)

    let write (st, i, o, Some r) = (st, i, o @ [r], None)

    let assign x (st, i, o, Some r) = (State.update x r st, i, o, None)

    let rec evalArgs e st = match e with
      | []        -> []
      | (e :: es) -> (Expr.eval st e) :: evalArgs es st

    let rec assignArgs vs xs st = match (vs, xs) with
      | ([], [])           -> st
      | (v :: vs, x :: xs) -> assignArgs vs xs (State.update x v st)

    let seq s1 s2 = match s2 with
      | Skip -> s1
      | _    -> Seq (s1, s2)
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt =
        match stmt, k with
        | Skip, Skip        -> (st, i, o, r)
        | Skip, k           -> eval env (st, i, o, r) Skip k
        | Assign (x, e), k  -> let (st1, i1, o1, r1) = Expr.eval env (st, i, o, r) e in
                                let c = assign x (st1, i1, o1, r1) in
                                eval env c Skip k
        | Write e, k        -> let (st1, i1, o1, r1) = Expr.eval env (st, i, o, r) e in
                                let c = write (st1, i1, o1, r1) in
                                eval env c Skip k
        | Read x, k         -> let c = read x (st, i, o, r) in
                                eval env c Skip k
        | If (e, t1, t2), k -> let (st1, i1, o1, Some r1) = Expr.eval env (st, i, o, r) e in
                                if r1 <> 0 then eval env (st1, i1, o1, None) k t1 else eval env (st1, i1, o1, None) k t2
        | While (e, t), k   -> let (st1, i1, o1, Some r1) = Expr.eval env (st, i, o, r) e in
                                if r1 <> 0 then eval env (st1, i1, o1, None) (Seq (While (e, t), k)) t else eval env (st1, i1, o1, None) Skip k
        | Repeat (t, e), k  -> let (st1, i1, o1, r1) = eval env (st, i, o, r) Skip t in
                                let (st2, i2, o2, Some r2) = Expr.eval env (st1, i1, o1, r1) e in
                                if r2 == 0 then eval env (st2, i2, o2, None) k (Repeat (t, e)) else eval env (st2, i2, o2, None) Skip k
        | Seq (t1, t2), k   -> eval env (st, i, o, r) (seq t2 k) t1
        | Call (f, args), k -> let c = Expr.eval env (st, i, o, r) (Expr.Call (f, args)) in
                                eval env c Skip k
        | Return (None), k  -> (st, i, o, r)
        | Return (Some e), k -> Expr.eval env (st, i, o, r) e
         
    (* Statement parser *)
    ostap (
      simple_stmt:
        x:IDENT ":=" c:!(Expr.parse) {Assign (x, c)}
      | f:IDENT "(" ars:!(args) ")" {Call (f, ars)}
      | "read" "(" x:IDENT ")"         {Read x}
      | "write" "(" c:!(Expr.parse) ")" {Write c}
      | "if" s1:!(elif) {Seq(s1, Skip)}
      | "while" c:!(Expr.parse) "do" s1:!(parse) "od" {While (c, s1)}
      | "repeat" s1:!(parse) "until" c:!(Expr.parse) {Repeat (s1, c)}
      | "for" s1:!(parse) "," c:!(Expr.parse) "," s2:!(parse) "do" s3:!(parse) "od" {Seq (s1, While (c, Seq(s3, s2)))}
      | "return" c:!(Expr.parse) {Return (Some c)}
      | "return" {Return None}
      | "skip" {Skip};

      elif: c:!(Expr.parse) "then" s1:!(parse) s2:!(else_branch)  {If (c, s1, s2)};
      else_branch: "fi" {Skip} | "else" s1:!(parse) "fi" {Seq (s1, Skip)} | "elif" s1:!(elif) {Seq (s1, Skip)};
      args: c:!(Expr.parse) "," left:!(args) {[c] @ left} | c:!(Expr.parse)  {[c]} | empty {[]};

      parse: <s::ss> : !(Ostap.Util.listBy)[ostap (";")][simple_stmt] {List.fold_left (fun s ss -> Seq (s, ss)) s ss}
)
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
