open GT       
open List
open Syntax
       
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

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval cfg prg = 
    let (stack, config) = cfg in
    let (state, inp, out) = config in
    let fst = nth stack 2 in
    let snd = hd stack in
    let rem = tl (tl stack) in
    let nextCfg = match hd prg with
        | BINOP op -> 
                let opResult = Expr.eval state (Expr.Binop (op, Expr.Const fst, Expr.Const snd)) in
                (opResult :: rem, config)
        | READ -> ((hd inp) :: stack, (state, tl inp, out))
        | WRITE -> (tl stack, (state, inp, append out [hd stack]))
        | LD name -> ((state name) :: stack, config)
        | ST name -> (tl stack, (Expr.update name (hd stack) state, inp, out))
    in eval nextCfg (tl prg)

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile = 
    let compExpr _ = failwith "Not yet implemented"
    in function
        | Stmt.Read x -> [READ; ST x]
        | Stmt.Write t -> append (compExpr t) [WRITE]
        | Stmt.Assign (name, ex) -> append (compExpr ex) [ST name]
        | Stmt.Seq (s1, s2) -> append (compile s1) (compile s2);;
