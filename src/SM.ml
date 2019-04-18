open GT       
open Language
       
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
        
let rec eval theEnv (controlStack, theStack, (theState, theInput, theOutput)) theProgram =
    match theProgram with
    | theInstruction :: prgrm -> (
        match theInstruction with
        | BINOP op ->
            let y :: x :: t = theStack in
            eval theEnv (controlStack, (Value.of_int @@ Language.Expr.to_func op (Value.to_int x) (Value.to_int y)) :: t, (theState, theInput, theOutput)) prgrm
        | CONST n -> eval theEnv (controlStack, (Value.of_int n) :: theStack, (theState, theInput, theOutput)) prgrm
        | STRING s -> eval theEnv (controlStack, (Value.of_string s) :: theStack, (theState, theInput, theOutput)) prgrm
        | LD x -> eval theEnv (controlStack, (Language.State.eval theState x) :: theStack, (theState, theInput, theOutput)) prgrm
        | ST x ->
            let h :: t = theStack in
            eval theEnv (controlStack, t, (Language.State.update x h theState, theInput, theOutput)) prgrm
        | STA (x, k) ->
            let (h :: t, tail) = split (k + 1) theStack in
            eval theEnv (controlStack, tail, (Stmt.update theState x h t, theInput, theOutput)) prgrm
        | LABEL l -> eval theEnv (controlStack, theStack, (theState, theInput, theOutput)) prgrm
        | JMP l -> eval theEnv (controlStack, theStack, (theState, theInput, theOutput)) (theEnv#labeled l)
        | CJMP (znz, l) ->
            let h :: t = theStack in
            if ((Value.to_int h) = 0 && znz = "z" || (Value.to_int h) <> 0 && znz = "nz") then
                eval theEnv (controlStack, t, (theState, theInput, theOutput)) (theEnv#labeled l)
            else
                eval theEnv (controlStack, t, (theState, theInput, theOutput)) prgrm
        | BEGIN (_, args, locals) ->
            let theState' = State.enter theState (args @ locals) in
            let theState'', theStack' = List.fold_left (fun (theState, x::theStack) name -> (State.update name x theState, theStack)) (theState', theStack) args in
            eval theEnv (controlStack, theStack', (theState'', theInput, theOutput)) prgrm
        | END
        | RET _ -> (
            match controlStack with
            | (prgrm', theState') :: controlStack' ->
                let theState'' = Language.State.leave theState theState' in
                eval theEnv (controlStack', theStack, (theState'', theInput, theOutput)) prgrm'
            | _ -> (controlStack, theStack, (theState, theInput, theOutput))
            )
        | CALL (f, n, fl) -> 
            if theEnv#is_label f
                then
                    eval theEnv ((prgrm, theState)::controlStack, theStack, (theState, theInput, theOutput)) (theEnv#labeled f)
                else
                    eval theEnv (theEnv#builtin (controlStack, theStack, (theState, theInput, theOutput)) f n (not fl)) prgrm
        )
    | [] -> (controlStack, theStack, (theState, theInput, theOutput));;

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
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) args f in
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
let label_generator =
    object
        val mutable counter = 0
        method generate_label = counter <- counter + 1;
        "label" ^ string_of_int counter
    end

let rec labeled_compilation_expr e =
    match e with
    | Language.Expr.Const theConst -> [CONST theConst]
    | Language.Expr.Array a ->
        let a' = List.flatten (List.map labeled_compilation_expr (List.rev a)) in
        a' @ [CALL ("$array", (List.length a'), true)]
    | Language.Expr.String s -> [STRING s]
    (*| Language.Expr.Sexp x, y -> ...*)
    | Language.Expr.Var theVariable -> [LD theVariable]
    | Language.Expr.Binop (theOp, leftOp, rightOp) ->
        let r1 = labeled_compilation_expr leftOp in
        let r2 = labeled_compilation_expr rightOp in
        r1 @ r2 @ [BINOP theOp]
    | Language.Expr.Elem (arr, index) -> labeled_compilation_expr index @ labeled_compilation_expr arr @ [CALL ("$elem", 2, true)]
    | Language.Expr.Length l -> labeled_compilation_expr l @ [CALL ("$length", 1, true)]
    | Language.Expr.Call (f, e) -> List.flatten (List.map labeled_compilation_expr (List.rev e)) @ [CALL (f, List.length e, true)];;

let rec labeled_compilation_stmt theProgram theLabel =
    match theProgram with
    | Language.Stmt.Assign (x, ids, e) -> (
        match ids with
        | [] -> (labeled_compilation_expr e @ [ST x]), false
        | _  ->
            let ids' = List.fold_left (fun p id -> p @ (labeled_compilation_expr id)) [] (List.rev ids) in
            ids' @ labeled_compilation_expr e @ [STA (x, List.length ids)], false
        )
    | Language.Stmt.Seq (s1, s2) ->
        let l2 = label_generator#generate_label in
        let (p1, label_is_used1) = labeled_compilation_stmt s1 l2 in
        let (p2, label_is_used2) = labeled_compilation_stmt s2 theLabel in
        (p1 @ (if label_is_used1 then [LABEL l2] else []) @ p2), label_is_used2
    | Language.Stmt.Skip -> [], false
    | Language.Stmt.If (e, s1, s2) ->
        let l2 = label_generator#generate_label in
        let (p1, label_is_used1) = labeled_compilation_stmt s1 theLabel in
        let (p2, label_is_used2) = labeled_compilation_stmt s2 theLabel in
        (labeled_compilation_expr e @
            [CJMP ("z", l2)] @
            p1 @ (if label_is_used1 then [] else [JMP theLabel]) @
            [LABEL l2] @
            p2 @ (if label_is_used2 then [] else [JMP theLabel])), true
    | Language.Stmt.While (e, s) ->
        let l2 = label_generator#generate_label in
        let l3 = label_generator#generate_label in
        let (body, _) = labeled_compilation_stmt s l2 in
        ([JMP l2; LABEL l3] @ body @ [LABEL l2] @ labeled_compilation_expr e @ [CJMP ("nz", l3)]), false
    | Language.Stmt.Repeat (s, e) ->
        let l2 = label_generator#generate_label in
        let (body, _) = labeled_compilation_stmt s theLabel in
        ([LABEL l2] @ body @ labeled_compilation_expr e @ [CJMP ("z", l2)]), false
    | Language.Stmt.Call (f, e) -> List.concat (List.map (labeled_compilation_expr) (List.rev e)) @ [CALL (f, List.length e, false)], false
    | Language.Stmt.Return e -> (
        match e with
        | Some ee -> (labeled_compilation_expr ee) @ [RET true], false
        | _ -> [RET false], false
        );;

let compileProgram theProgram =
    let theLabel = label_generator#generate_label in
    let theProgram', label_is_used = labeled_compilation_stmt theProgram theLabel in
    theProgram' @ (if label_is_used then [LABEL theLabel] else []);;

let compileDefs theDefinitions =
    let compileDef (f, (args, locals, body)) = 
        (let body' = compileProgram body in
        [LABEL f; BEGIN (f, args, locals)] @ body' @ [END])
    in
    List.flatten (List.map compileDef theDefinitions);;

let rec compile (theDefinitions, theProgram) =
    let theProgram' = compileProgram theProgram in
    let theDefinitions' = compileDefs theDefinitions in
    theProgram' @ [END] @ theDefinitions';;
