open GT       
open Language
       
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
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         

let eval_other (controlStack, theStack, (theState, theInput, theOutput)) theInstruction =
    match theInstruction with
    | BINOP op -> (
        match theStack with
        | y :: x :: t -> (controlStack, (Language.Expr.to_func op x y) :: t, (theState, theInput, theOutput)))
    | CONST n -> (controlStack, n :: theStack, (theState, theInput, theOutput))
    | READ -> (
        match theInput with
        | h :: t -> (controlStack, h :: theStack, (theState, t, theOutput)))
    | WRITE -> (
        match theStack with
        | h :: t -> (controlStack, t, (theState, theInput, theOutput @ [h])))
    | LD x -> (controlStack, (Language.State.eval theState x) :: theStack, (theState, theInput, theOutput))
    | ST x -> (
        match theStack with
        | h :: t -> (controlStack, t, (Language.State.update x h theState, theInput, theOutput)))
    | LABEL l -> (controlStack, theStack, (theState, theInput, theOutput));;

let rec eval theEnv (controlStack, theStack, (theState, theInput, theOutput)) theProgram =
    match theProgram with
    | theInstruction :: prgrm -> (
        match theInstruction with
        | JMP l -> eval theEnv (controlStack, theStack, (theState, theInput, theOutput)) (theEnv#labeled l)
        | CJMP (znz, l) -> (
            match theStack with
            | h :: t ->
                if (h = 0 && znz = "nz" || h <> 0 && znz = "z") then
                    eval theEnv (controlStack, theStack, (theState, theInput, theOutput)) prgrm
                else
                    eval theEnv (controlStack, theStack, (theState, theInput, theOutput)) (theEnv#labeled l)
            )
        | BEGIN (args, locals) ->
            let theState' = Language.State.push_scope theState (args @ locals) in 
            let args' = List.map (fun p -> ST p) args in
            let theConfig' = eval theEnv (controlStack, theStack, (theState', theInput, theOutput)) args' in
            eval theEnv theConfig' prgrm
        | END -> (
            match controlStack with
            | (prgrm', theState') :: controlStack' ->
                let theState'' = Language.State.drop_scope theState theState' in
                eval theEnv (controlStack', theStack, (theState'', theInput, theOutput)) prgrm'
            | _ -> (controlStack, theStack, (theState, theInput, theOutput))
            )
        | CALL l -> eval theEnv ((prgrm, theState) :: controlStack, theStack, (theState, theInput, theOutput)) (theEnv#labeled l)
        | _ -> eval theEnv (eval_other (controlStack, theStack, (theState, theInput, theOutput)) theInstruction) prgrm)
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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

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
    | Language.Expr.Var theVariable -> [LD theVariable]
    | Language.Expr.Binop (theOp, leftOp, rightOp) ->
        let r1 = labeled_compilation_expr leftOp in
        let r2 = labeled_compilation_expr rightOp in
        r1 @ r2 @ [BINOP theOp];;

let rec labeled_compilation_stmt theProgram theLabel =
    match theProgram with
    | Language.Stmt.Read x -> [READ; ST x], false
    | Language.Stmt.Write e -> (labeled_compilation_expr e @ [WRITE]), false
    | Language.Stmt.Assign (x, e) -> (labeled_compilation_expr e @ [ST x]), false
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
    | Language.Stmt.Call (f, e) -> List.concat (List.map (labeled_compilation_expr) (List.rev e)) @ [CALL f], false;;

let compileProgram theProgram =
    let theLabel = label_generator#generate_label in
    let theProgram', label_is_used = labeled_compilation_stmt theProgram theLabel in
    theProgram' @ (if label_is_used then [LABEL theLabel] else []);;

let compileDefs theDefinitions =
    let compileDef (f, (args, locals, body)) = 
        (let body' = compileProgram body in
        [LABEL f; BEGIN (args, locals)] @ body' @ [END])
    in
    List.flatten (List.map compileDef theDefinitions);;

let rec compile (theDefinitions, theProgram) =
    let theProgram' = compileProgram theProgram in
    let theDefinitions' = compileDefs theDefinitions in
    theProgram' @ [END] @ theDefinitions';;
