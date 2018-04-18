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

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

    let evalBinop op a b = match op with
    | "+" -> a + b
    | "-" -> a - b
    | "*" -> a * b
    | "/" -> a / b
    | "%" -> a mod b
    | "<" -> if a < b then 1 else 0
    | ">" -> if a > b then 1 else 0
    | ">=" -> if a >= b then 1 else 0
    | "<=" -> if a <= b then 1 else 0
    | "==" -> if a == b then 1 else 0
    | "!=" -> if a != b then 1 else 0
    | "&&" -> if a != 0 && b != 0 then 1 else 0
    | "!!" -> if a != 0 || b != 0 then 1 else 0;;


    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
    *)
    let rec eval env ((st, i, o, r) as conf) = function
        | Const r -> st, i, o, Some r
        | Var s -> st, i, o, Some (State.eval st s)
        | Binop (op, a, b) ->
                let ( _, _, _, Some a) as conf = eval env conf a in
                let (st, i, o, Some b) as conf = eval env conf b in
                st, i, o, Some (evalBinop op a b)
        | Call (name, args) ->
                let evalArg (argv, conf) argEx = let (_, _, _, Some r) as conf = eval env conf argEx in r :: argv, conf in
                let argv, conf = fold_left evalArg ([], conf) args in
                env#definition env name (rev argv) conf
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list * int option

    (* Statement evaluator

           val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k =
        let proceed st i o = let conf = (st, i, o, None) in match k with | Skip -> conf | _ -> eval env conf k Skip in
        function
        | Read s -> proceed (State.update s (hd i) st) (tl i) o
        | Write ex -> let st, i, o, Some r = Expr.eval env conf ex in proceed st i (append o [r])
        | Assign (var, ex) -> let st, i, o, Some r = Expr.eval env conf ex in proceed (State.update var r st) i o
        | Seq (s1, s2) -> let (st, i, o, _) = eval env conf s1 s2 in proceed st i o
        | Skip -> proceed st i o
        | If (cond, tbrc, fbrc) -> let (st, i, o, Some r) as conf = Expr.eval env conf cond in eval env (st, i, o, None) (if r != 0 then tbrc else fbrc) k
        | While (cond, body) as stmt ->
                let (st, i, o, Some r) as conf = Expr.eval env conf cond in
                if r != 0 then eval env conf body (Seq (stmt, k)) else proceed st i o
        | Return None      -> (st, i, o, None)
        | Return (Some ex) -> Expr.eval env conf ex
        | Call (name, args) -> let (st, i, o, _) = Expr.eval env conf (Expr.Call (name, args)) in proceed st i o;;

    (* Statement parser *)
    ostap (
      parse: !(Util.list0ByWith)[ostap (";")][singleOp][fun x h -> Seq (x, h)][Skip];
      singleOp: assign | skip | cond | whle | repeat | foreach | read | write | call;
      assign: x:IDENT ":=" ex:!(Expr.parse) {Assign (x, ex)};
      skip: "skip" {Skip};
      cond: "if" c:!(Expr.parse) "then" t:parse f:condElse {If (c, t, f)};
      condElse: "elif" c:!(Expr.parse) "then" t:parse f:condElse {If (c, t, f)} | -"else" parse -"fi" | "fi" {Skip};
      whle: "while" c:!(Expr.parse) "do" b:parse "od" {While (c, b)};
      repeat: "repeat" b:parse "until" c:!(Expr.parse) {Seq (b, While (Expr.Binop ("==", c, Expr.Const 0), b))};
      foreach: "for" ini:parse "," c:!(Expr.parse) "," inc:parse "do" b:parse "od" {Seq (ini, While (c, Seq (b, inc)))};
      read: "read" "(" s:IDENT ")" {Read s};
      write: "write" ex:!(Expr.parent) {Write ex};
      return: "return" ex:!(Expr.parse)? {Return ex};
      call: name:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (name, args)}
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
