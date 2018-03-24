(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

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

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval st ex = 
        match ex with
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
    (* loop with a post-condition       *) (* add yourself *)  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval cfg st = 
        let (state, inp, out) = cfg in
        match st with
        | Read s -> ((Expr.update s (hd inp) state), (tl inp), out)
        | Write ex -> (state, inp, (append out [Expr.eval state ex]))
        | Assign (var, ex) -> ((Expr.update var (Expr.eval state ex) state), inp, out)
        | Seq (s1, s2) -> eval (eval cfg s1) s2;;

    (* Statement parser *)
    ostap (
      parse: f:singleOp ";" s:parse {Seq (f, s)} | singleOp;
      singleOp: "read" "(" s:IDENT ")" {Read s} | "write" ex:!(Expr.parent) {Write ex} | x:IDENT ":=" ex:!(Expr.parse) {Assign (x, ex)}
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

(* Top-level parser *)
let parse = Stmt.parse
