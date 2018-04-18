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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show

(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
    | [] -> conf
    | cInst :: progRem ->
        let cCfg, cont = match (cInst, cstack) with
        | BINOP op, _                   ->
                let x :: y :: stack = stack in
                let calcResult = Expr.eval st (Expr.Binop (op, Expr.Const y, Expr.Const x)) in
                (cstack, calcResult :: stack, c), progRem
        | CONST v, _                    -> (cstack, v :: stack, c), progRem
        | READ, _                       ->
                let r :: cInp = i in
                (cstack, r :: stack, (st, cInp, o)), progRem
        | WRITE, _                      -> let x :: stack = stack in (cstack, stack, (st, i, append o [x])), progRem
        | LD name, _                    -> (cstack, State.eval st name :: stack, c), progRem
        | ST name, _                    -> let x :: stack = stack in (cstack, stack, (State.update name x st, i, o)), progRem
        | LABEL name, _                 -> conf, progRem
        | JMP name, _                   -> conf, env#labeled name
        | CJMP ("z", name), _           -> let x :: stack = stack in (cstack, stack, c), if x == 0 then env#labeled name else progRem
        | CJMP ("nz", name), _          -> let x :: stack = stack in (cstack, stack, c), if x != 0 then env#labeled name else progRem
        | BEGIN (args, locals), _       ->
                let st = fold_right2 State.update args stack (State.enter st (append args locals)) in
                let rec drop n l = if n == 0 then l else drop (n - 1) (tl l) in
                let stack = drop (length args) stack in
                (cstack, stack, (st, i, o)), progRem
        | END, (progRem, oSt) :: cstack -> (cstack, stack, (State.leave st oSt, i, o)), progRem
        | END, []                       -> conf, []
        | CALL name, _                  -> ((progRem, st) :: cstack, stack, c), env#labeled name
        in
        eval env cCfg cont

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, stmt) =
    let rec compExpr = function
        | Expr.Const x -> [CONST x]
        | Expr.Var s -> [LD s]
        | Expr.Binop (op, f, s) -> append (compExpr f) (append (compExpr s) [BINOP op])
    in
    let getLabel cNum = "__l" ^ string_of_int cNum, cNum + 1 in
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
        | Stmt.Call (name, args) -> append (concat (rev_map compExpr args)) [CALL name], lState
    in
    let result, lState = compileImpl 0 stmt in
    let compileFunc (result, lState) (name, (args, locals, body)) =
        let (compDef, lState) = compileImpl lState body in
        append result (append (LABEL name :: BEGIN (args, locals) :: compDef) [END]), lState
    in
    let result, lState = fold_left compileFunc (append result [END], lState) defs in
    result
