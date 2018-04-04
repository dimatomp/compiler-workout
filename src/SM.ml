open GT       
open Language
open List
       
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

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env conf = function
    | [] -> conf
    | cInst :: progRem -> 
        let stack, sCfg = conf in
        let vars, inp, out = sCfg in
        let cCfg, cont = match cInst with
        | BINOP op          -> 
                let x :: y :: rem = stack in 
                let calcResult = Expr.eval vars (Expr.Binop (op, Expr.Const y, Expr.Const x)) in
                (calcResult :: rem, sCfg), progRem
        | CONST v           -> (v :: stack, sCfg), progRem
        | READ              -> 
                let r :: cInp = inp in 
                (r :: stack, (vars, cInp, out)), progRem
        | WRITE             -> let x :: rem = stack in (rem, (vars, inp, x :: out)), progRem
        | LD name           -> (vars name :: stack, sCfg), progRem 
        | ST name           -> let x :: rem = stack in (rem, (Expr.update name x vars, inp, out)), progRem
        | LABEL name        -> conf, progRem
        | JMP name          -> conf, env#labeled name
        | CJMP ("z", name)  -> let x :: rem = stack in (rem, sCfg), if x == 0 then env#labeled name else progRem
        | CJMP ("nz", name) -> let x :: rem = stack in (rem, sCfg), if x != 0 then env#labeled name else progRem
        in 
        eval env cCfg cont

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

(* Stack machine jompiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let compile stmt = 
    let rec compExpr = function
        | Expr.Const x -> [CONST x]
        | Expr.Var s -> [LD s]
        | Expr.Binop (op, f, s) -> append (compExpr f) (append (compExpr s) [BINOP op])
    in
    let getLabel cNum = "l" ^ string_of_int cNum, cNum + 1 in
    let rec compileImpl lState = function
        | Stmt.Read x -> [READ; ST x], lState
        | Stmt.Write t -> append (compExpr t) [WRITE], lState
        | Stmt.Assign (name, ex) -> append (compExpr ex) [ST name], lState
        | Stmt.Seq (s1, s2) -> 
                let code1, lState = compileImpl lState s1 in
                let code2, lState = compileImpl lState s2 in
                append code1 code2, lState
        | Stmt.Skip -> ([], lState)
        | Stmt.If (cond, tBrc, fBrc) -> 
                let condition = compExpr cond in
                let trueBranch, lState = compileImpl lState tBrc in
                let falseBranch, lState = compileImpl lState fBrc in
                let fLabel, lState = getLabel lState in
                let sLabel, lState = getLabel lState in
                append condition (append (CJMP ("z", fLabel) :: trueBranch) (append (JMP sLabel :: LABEL fLabel :: falseBranch) [LABEL sLabel])), lState
        | Stmt.While (cond, body) ->
                let condition = compExpr cond in
                let bodyCode, lState = compileImpl lState body in
                let sLabel, lState = getLabel lState in
                let fLabel, lState = getLabel lState in
                append (LABEL sLabel :: condition) (append (CJMP ("z", fLabel) :: bodyCode) [JMP sLabel; LABEL fLabel]), lState
        | Stmt.For (init, cond, incr, body) -> 
                let initCode, lState = compileImpl lState init in
                let bodyCode, lState = compileImpl lState (Stmt.While (cond, Stmt.Seq (body, incr))) in
                append initCode bodyCode, lState
    in
    let (result, _) = compileImpl 0 stmt in
    result
