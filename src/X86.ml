(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string
                                                                            
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM
open List

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let rec compile env = function
    | [] -> env, []
    | inst::rem -> 
            let env, cInst = match inst with
            | BINOP name -> let y, x, env = env#pop2 in
                            let comparison c = [Mov (x, eax); Binop("-", y, eax); Set (c, "%al"); Binop ("&&", L 1, eax); Mov (eax, x)] in
                            let divmod reg = [Mov (x, eax); Cltd; IDiv y; Mov (reg, x)] in
                            let commands = match name with
                            | "/" -> divmod eax
                            | "%" -> divmod edx
                            | "<" -> comparison "l"
                            | "<=" -> comparison "le"
                            | ">" -> comparison "g"
                            | ">=" -> comparison "ge"
                            | "==" -> comparison "e"
                            | "!=" -> comparison "ne"
                            | "!!" -> [Mov (x, eax); Binop("!!", y, eax); Set ("nz", "%al"); Binop ("&&", L 1, eax); Mov (eax, x)]
                            | "&&" -> [Mov (y, eax); Binop("&&", eax, eax); Set ("nz", "%al"); Mov (x, edx); Binop ("&&", edx, edx); Set ("nz", "%ah"); Binop ("&&", L 257, eax); Binop ("^", L 257, eax); Set ("z", "%al"); Binop ("&&", L 1, eax); Mov (eax, x)]
                            | _ -> [Mov (x, eax); Binop (name, y, eax); Mov (eax, x)]
                            in env#push x, commands
            | CONST cst -> let x, env = env#allocate in env, [Mov (L cst, x)]
            | READ -> let x, env = env#allocate in env, [Call "Lread"; Mov (eax, x)]
            | WRITE -> let x, env = env#pop in env, [Mov (x, eax); Push eax; Call "Lwrite"; Binop ("+", L 4, esp)]
            | LD name -> let env = env#global name in let x, env = env#allocate in env, [Mov (env#loc name, eax); Mov (eax, x)]
            | ST name -> let x, env = (env#global name)#pop in env, [Mov (x, eax); Mov (eax, env#loc name)]
            | LABEL name -> env, [Label name]
            | JMP name -> env, [Jmp name]
            | CJMP (cnd, name) -> let x, env = env#pop in env, [Mov (x, eax); Binop ("&&", eax, eax); CJmp (cnd, name)]
            | BEGIN (name, args, locals) -> env#enter name args locals, [Push ebp; Mov (esp, ebp)]
            | RET true -> let x, env = env#pop in env, [Mov (x, eax); Pop ebp; Ret]
            | RET false -> env, [Pop ebp; Ret]
            | CALL (name, arglen, func) -> 
                    let rec argStrip env = function
                        | 0 -> [], env
                        | n -> let x, env = env#pop in let l, env = argStrip env (n - 1) in x :: l, env
                    in
                    let args, env = argStrip env arglen in
                    let liveRegs = env#live_registers in
                    let alignEspAndPushLiveRegs = Mov (ebp, esp) :: Binop ("-", L (4 * env#allocated), esp) :: map (fun x -> Push x) liveRegs in
                    let pushArgs = concat (map (fun x -> [Mov (x, eax); Push eax]) args) in
                    let callFunction, env = if func then let x, env = env#allocate in [Call name; Mov (eax, x)], env else [Call name], env in
                    let removeArgsAndPopLiveRegs = (Binop ("+", L (4 * arglen), esp) :: rev_map (fun x -> Pop x) liveRegs) in
                    env, (alignEspAndPushLiveRegs @ pushArgs @ callFunction @ removeArgsAndPopLiveRegs)
            in
            let env, rInst = compile env rem in 
            env, cInst @ rInst

(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
let make_assoc l = List.combine l (List.init (List.length l) (fun x -> x))
                     
class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
                        
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
	let rec allocate' = function
	| []                            -> ebx     , 0
	| (S n)::_                      -> S (n+1) , n+1
	| (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (M _)::s                      -> allocate' s
	| _                             -> S 0     , 1
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack
      
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
