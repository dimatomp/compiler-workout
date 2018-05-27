open GT
open Language
open List

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
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
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern lfalse = function
  | Stmt.Pattern.Wildcard -> []
  | Stmt.Pattern.Ident s -> [ST s]
  | Stmt.Pattern.Sexp (name, args) -> DUP :: TAG name :: CJMP ("z", lfalse) :: bindings args lfalse
  and bindings p lfalse = 
    let rec compareArgs lnum = function
    | [] -> [DROP]
    | arg::rem -> DUP :: CONST lnum :: SWAP :: CALL (".elem", 2, false) :: pattern lfalse arg @ compareArgs (lnum + 1) rem
    in compareArgs 0 p
  and expr = function
  | Expr.Const n -> [CONST n]
  | Expr.String s -> [STRING s]
  | Expr.Sexp (name, args) -> concat (map expr args) @ [SEXP (name, length args)]
  | Expr.Var name -> [LD name]
  | Expr.Binop (op, a, b) -> expr a @ expr b @ [BINOP op]
  | Expr.Call (name, args) -> call name args false
  in
  let rec compile_stmt l env = function
  | Stmt.Assign (var, [], ex) -> env, true, expr ex @ [ST var]
  | Stmt.Assign (var, idx, ex) -> env, true, concat (map expr idx) @ expr ex @ [STA (var, length idx)]
  | Stmt.Seq (e1, e2) -> 
          let env, true, c1 = compile_stmt l env e1 in
          let env, true, c2 = compile_stmt l env e2 in
          env, true, c1 @ c2
  | Stmt.Skip -> env, true, []
  | Stmt.If (cond, tbrc, fbrc) ->
          let condCode = expr cond in
          let fBranch, env = env#get_label in
          let ifEnd, env = env#get_label in
          let env, true, trueCode = compile_stmt l env tbrc in
          let env, true, trueCode = compile_stmt l env fbrc in
          env, true, condCode @ [CJMP ("z", fBranch)] @ trueCode @ [JMP ifEnd; LABEL fBranch] @ trueCode @ [LABEL ifEnd]
  | Stmt.Leave -> env, true, [LEAVE]
  | Stmt.While (cond, body) -> 
          let wBegin, env = env#get_label in 
          let condCode = expr cond in
          let wEnd, env = env#get_label in
          let env, true, bodyCode = compile_stmt l env body in
          env, true, (LABEL wBegin :: condCode) @ [CJMP ("z", wEnd)] @ bodyCode @ [JMP wBegin]
  | Stmt.Return None -> env, true, [JMP l]
  | Stmt.Return (Some ex) -> env, true, expr ex @ [JMP l]
  | Stmt.Call (name, args) -> env, true, call name args true
  | Stmt.Case (ex, patterns) ->
          let exCode = expr ex in
          let retLabel, env = env#get_label in
          let exitLabel, env = env#get_label in
          let genCase (env, caseBody) (pat, body) = 
            let nonMatched, env = env#get_label in
            let env, true, bodyCode = compile_stmt retLabel env body in
            env, caseBody @ ENTER (Stmt.Pattern.vars pat) :: pattern retLabel pat @ bodyCode @ [JMP exitLabel; LABEL nonMatched; LEAVE]
          in
          let env, cases = fold_left genCase (env, []) patterns in
          env, true, exCode @ cases @ [LABEL retLabel; LEAVE; JMP l; LABEL exitLabel; LEAVE]
  in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 
