(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty = failwith "Not implemented"

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = failwith "Not implemented"
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = failwith "Not implemented" 

    (* Creates a new scope, based on a given state *)
    let enter st xs = failwith "Not implemented"

    (* Drops a scope *)
    let leave st st' = failwith "Not implemented"

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval st = function
        | Const i -> i
        | Var s -> st s
        | Binop ("+", a, b) -> eval st a + eval st b
        | Binop ("-", a, b) -> eval st a - eval st b
        | Binop ("*", a, b) -> eval st a * eval st b
        | Binop ("/", a, b) -> eval st a / eval st b
        | Binop ("%", a, b) -> eval st a mod eval st b
        | Binop ("<", a, b) -> if eval st a < eval st b then 1 else 0
        | Binop (">", a, b) -> if eval st a > eval st b then 1 else 0
        | Binop ("<=", a, b) -> if eval st a <= eval st b then 1 else 0
        | Binop (">=", a, b) -> if eval st a >= eval st b then 1 else 0
        | Binop ("==", a, b) -> if eval st a == eval st b then 1 else 0
        | Binop ("!=", a, b) -> if eval st a != eval st b then 1 else 0
        | Binop ("&&", a, b) -> if eval st a != 0 && eval st b != 0 then 1 else 0
        | Binop ("!!", a, b) -> if eval st a != 0 || eval st b != 0 then 1 else 0
        | v -> failwith "invalid syntax";;

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      parse: !(Ostap.Util.expr                                         
                (fun x -> x)                                     
                (Array.map (fun (a, s) -> a, List.map (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s) 
                  [|
                    `Lefta, ["!!"];
                    `Lefta, ["&&"];
                    `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
                    `Lefta, ["+" ; "-"];
                    `Lefta, ["*" ; "/"; "%"];
                  |] 
                )
                primary                                          
              );
      primary: n:IDENT {Var n} | x:DECIMAL {Const x} | parent;
      parent: -"(" parse -")"
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
    (* call a procedure                 *) | Call   of string * Expr.t list with show
    (* loop with a post-condition       *) | For    of t * Expr.t * t * t  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

           val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let eval env ((st, i, o) as conf) = function
        | Read s -> ((Expr.update s (hd i) st), (tl i), o)
        | Write ex -> (st, i, (append o [Expr.eval st ex]))
        | Assign (var, ex) -> ((Expr.update var (Expr.eval st ex) st), i, o)
        | Seq (s1, s2) -> eval (eval conf s1) s2
        | Skip -> conf
        | If (cond, tbrc, fbrc) -> eval conf (if Expr.eval st cond != 0 then tbrc else fbrc)
        | While (cond, body) -> if Expr.eval st cond == 0 then conf else eval (eval conf body) st
        | For (init, cond, incr, body) -> 
                let conf1 = eval conf init in
                if Expr.eval st cond == 0 then conf1 else eval (eval (eval conf1 body) incr) st;;

    (* Statement parser *)
    ostap (
      parse: f:singleOp ";" s:parse {Seq (f, s)} | singleOp;
      singleOp: read | write | assign | skip | cond | whle | repeat | foreach;
      read: "read" "(" s:IDENT ")" {Read s};
      write: "write" ex:!(Expr.parent) {Write ex};
      assign: x:IDENT ":=" ex:!(Expr.parse) {Assign (x, ex)};
      skip: "skip" {Skip};
      cond: "if" c:!(Expr.parse) "then" t:parse f:condElse {If (c, t, f)};
      condElse: "elif" c:!(Expr.parse) "then" t:parse f:condElse {If (c, t, f)} | "fi" {Skip};
      whle: "while" c:!(Expr.parse) "do" b:parse "od" {While (c, b)};
      repeat: "repeat" b:parse "until" c:!(Expr.parse) {Seq (b, While (c, b))};
      foreach: "for" ini:parse "," c:!(Expr.parse) "," inc:parse "do" b:parse "od" {For (ini, c, inc, b)}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: empty {failwith "Not implemented"}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i = failwith "Not implemented"
                                   
(* Top-level parser *)
let parse = failwith "Not implemented"
