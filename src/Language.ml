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
    let empty = { g = failwith "No such global variable"; l = failwith "Local variable no initialized"; scope = [] }

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = 
        let updateFun f = fun s -> if s == x then v else f s in
        if mem x s.scope then { s with l = updateFun s.l; } else { s with g = updateFun s.g; }
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = { empty with g = st.g; scope = xs; }

    (* Drops a scope *)
    let leave st st' = { st' with g = st.g; }

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
        | Var s -> State.eval st s
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
    (* call a procedure                 *) | Call   of string * Expr.t list
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
    let rec eval env ((st, i, o) as conf) = function
        | Read s -> ((State.update s (hd i) st), (tl i), o)
        | Write ex -> (st, i, (append o [Expr.eval st ex]))
        | Assign (var, ex) -> ((State.update var (Expr.eval st ex) st), i, o)
        | Seq (s1, s2) -> eval env (eval env conf s1) s2
        | Skip -> conf
        | If (cond, tbrc, fbrc) -> eval env conf (if Expr.eval st cond != 0 then tbrc else fbrc)
        | While (cond, body) as stmt -> if Expr.eval st cond == 0 then conf else eval env (eval env conf body) stmt
        | Repeat (body, cond) -> eval env conf (Seq (body, While (cond, body)))
        | For (init, cond, incr, body) as stmt -> 
                let conf1 = eval env conf init in
                if Expr.eval st cond == 0 then conf1 else eval env (eval env (eval env conf1 body) incr) stmt
        | Call (name, args) -> 
                let argNames, localNames, body = env#definition name in
                let argValues = List.map (Expr.eval st) args in
                let nSt = fold_left2 (fun s x v -> State.update x v s) (State.enter st (append argNames localNames)) argNames argValues in
                let nSt, i, o = eval env (nSt, i, o) body in
                State.leave nSt st, i, o;;

    (* Statement parser *)
    ostap (
      parse: !(Util.list0ByWith)[ostap (";")][singleOp][fun x h -> Seq (x, h)][Skip];
      singleOp: read | write | assign | skip | cond | whle | repeat | foreach | call;
      read: "read" "(" s:IDENT ")" {Read s};
      write: "write" ex:!(Expr.parent) {Write ex};
      assign: x:IDENT ":=" ex:!(Expr.parse) {Assign (x, ex)};
      skip: "skip" {Skip};
      cond: "if" c:!(Expr.parse) "then" t:parse f:condElse {If (c, t, f)};
      condElse: "elif" c:!(Expr.parse) "then" t:parse f:condElse {If (c, t, f)} | "fi" {Skip};
      whle: "while" c:!(Expr.parse) "do" b:parse "od" {While (c, b)};
      repeat: "repeat" b:parse "until" c:!(Expr.parse) {Repeat (b, c)};
      foreach: "for" ini:parse "," c:!(Expr.parse) "," inc:parse "do" b:parse "od" {For (ini, c, inc, b)};
      call: name:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (name, args)}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: "fun" name:IDENT "(" args:!(Util.list0)[ostap (IDENT)] ")" locals:(loc:(-"locals" !(Util.list)[ostap (IDENT)])? {match loc with None -> [] | Some loc -> loc}) "{" body:!(Stmt.parse) "}" {name, (args, locals, body)}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i = let _, _, o = Stmt.eval (object method definition s = assoc s defs end) (State.empty, i, []) body in o
                                   
(* Top-level parser *)
ostap (
  parse: defs:!(Definition.parse)* body:!(Stmt.parse) {defs, body}
)
