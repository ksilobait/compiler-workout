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

let eval_other (theStack, (theState, theInput, theOutput)) theInstruction =
    match theInstruction with
    | BINOP op -> (
        match theStack with
        | y :: x :: t -> ((Language.Expr.processBinop op x y) :: t, (theState, theInput, theOutput)))
    | CONST n -> (n :: theStack, (theState, theInput, theOutput))
    | READ -> (
        match theInput with
        | h :: t -> (h :: theStack, (theState, t, theOutput)))
    | WRITE -> (
        match theStack with
        | h :: t -> (t, (theState, theInput, theOutput @ [h])))
    | LD x -> ((theState x) :: theStack, (theState, theInput, theOutput))
    | ST x -> (
        match theStack with
        | h :: t -> (t, (Language.Expr.update x h theState, theInput, theOutput)));;

let rec eval theEnv theConfig theProgram =
    match theProgram with
    | theInstruction :: prgrm -> (
        match theInstruction with
        | LABEL l -> eval theEnv theConfig prgrm
        | JMP l -> eval theEnv theConfig (theEnv#labeled l)
        | CJMP (znz, l) -> (
            let (theStack, _) = theConfig in
            match theStack with
            | h :: t ->
                if (h = 0 && znz = "nz" || h <> 0 && znz = "z") then
                    eval theEnv theConfig prgrm
                else
                    eval theEnv theConfig (theEnv#labeled l))
        | _ -> eval theEnv (eval_other theConfig theInstruction) prgrm)
    | [] -> theConfig;;


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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Language.Expr.empty, i, [])) p in o


let label_generator =
    object
        val mutable counter = 0
        method generate_label = counter <- counter + 1;
        "label" ^ string_of_int counter
    end
(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
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
    | Language.Stmt.RepeatUntil (s, e) ->
        let l2 = label_generator#generate_label in
        let (body, _) = labeled_compilation_stmt s theLabel in
        ([LABEL l2] @ body @ labeled_compilation_expr e @ [CJMP ("z", l2)]), false;;

let rec compile theProgram =
    let theLabel = label_generator#generate_label in
    let theProgram', label_is_used = labeled_compilation_stmt theProgram theLabel in
    theProgram' @ (if label_is_used then [LABEL theLabel] else []);;
