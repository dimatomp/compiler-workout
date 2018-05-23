open GT
open Language
open List

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
    | [] -> conf
    | cInst :: progRem ->
        let cCfg, cont = match (cInst, cstack) with
        | BINOP op, _                                 ->
                let x :: y :: stack = stack in
                let calcResult = Value.of_int @@ Expr.evalBinop op (Value.to_int y) (Value.to_int x) in
                (cstack, calcResult :: stack, c), progRem
        | CONST v, _                                  -> (cstack, Value.of_int v :: stack, c), progRem
        | STRING v, _                                 -> (cstack, Value.of_string v :: stack, c), progRem
        | LD name, _                                  -> (cstack, State.eval st name :: stack, c), progRem
        | ST name, _                                  -> let x :: stack = stack in (cstack, stack, (State.update name x st, i, o)), progRem
        | STA (name, indices), _                      ->
                let x :: stack = stack in
                let indices, stack = split indices stack in
                (cstack, stack, (Stmt.update st name x (rev indices), i, o)), progRem
        | LABEL name, _                               -> conf, progRem
        | JMP name, _                                 -> conf, env#labeled name
        | CJMP ("z", name), _                         -> let x :: stack = stack in (cstack, stack, c), if Value.to_int x == 0 then env#labeled name else progRem
        | CJMP ("nz", name), _                        -> let x :: stack = stack in (cstack, stack, c), if Value.to_int x != 0 then env#labeled name else progRem
        | BEGIN (_, args, locals), _                  ->
                let argv, stack = split (length args) stack in
                let st = fold_right2 State.update (rev args) argv (State.enter st (args @ locals)) in
                (cstack, stack, (st, i, o)), progRem
        | RET _, (progRem, oSt) :: cstack             -> (cstack, stack, (State.leave st oSt, i, o)), progRem
        | RET _, []                                   -> conf, []
        | CALL (name, n, f), _ when env#is_label name -> ((progRem, st) :: cstack, stack, c), env#labeled name
        | CALL (name, n, f), _                        -> env#builtin conf name n (not f), progRem
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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, stmt) =
    let genCall compExpr name args func = (concat (map compExpr args)) @ [CALL (name, length args, func)] in
    let rec compExpr = function
        | Expr.Const x -> [CONST x]
        | Expr.String s -> [STRING s]
        | Expr.Var s -> [LD s]
        | Expr.Binop (op, f, s) -> (compExpr f) @ (compExpr s) @ [BINOP op]
        | Expr.Call (name, args) -> genCall compExpr name args true
    in
    let getLabel cNum = "__l" ^ string_of_int cNum, cNum + 1 in
    let rec compileImpl lState = function
        | Stmt.Assign (name, [], ex) -> (compExpr ex) @ [ST name], lState
        | Stmt.Assign (name, l, ex) -> (concat (map compExpr l)) @ (compExpr ex) @ [STA (name, length l)], lState
        | Stmt.Seq (s1, s2) ->
                let code1, lState = compileImpl lState s1 in
                let code2, lState = compileImpl lState s2 in
                code1 @ code2, lState
        | Stmt.Skip -> ([], lState)
        | Stmt.If (cond, tBrc, fBrc) ->
                let condition = compExpr cond in
                let trueBranch, lState = compileImpl lState tBrc in
                let falseBranch, lState = compileImpl lState fBrc in
                let fLabel, lState = getLabel lState in
                let sLabel, lState = getLabel lState in
                condition @ (CJMP ("z", fLabel) :: trueBranch) @ (JMP sLabel :: LABEL fLabel :: falseBranch) @ [LABEL sLabel], lState
        | Stmt.While (cond, body) ->
                let condition = compExpr cond in
                let bodyCode, lState = compileImpl lState body in
                let sLabel, lState = getLabel lState in
                let fLabel, lState = getLabel lState in
                (LABEL sLabel :: condition) @ (CJMP ("z", fLabel) :: bodyCode) @ [JMP sLabel; LABEL fLabel], lState
        | Stmt.Return None -> [RET false], lState
        | Stmt.Return (Some expr) -> (compExpr expr) @ [RET true], lState
        | Stmt.Call (name, args) -> genCall compExpr name args false, lState
    in
    let result, lState = compileImpl 0 stmt in
    let compileFunc (result, lState) (name, (args, locals, body)) =
        let (compDef, lState) = compileImpl lState body in
        result @ (LABEL name :: BEGIN (name, args, locals) :: compDef) @ [RET false], lState
    in
    let result, lState = fold_left compileFunc (result @ [RET false], lState) defs in
    result
