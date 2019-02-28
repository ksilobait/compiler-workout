open GT       
       
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
type config = int list * Syntax.Stmt.config

let evalStep (theStack, (theState, theInput, theOutput)) theProgram =
    match theProgram with
    | BINOP op -> (
        match theStack with
        | y :: x :: t -> ([Syntax.Expr.processBinop op x y] @ t, (theState, theInput, theOutput)))
    | CONST n -> ([n] @ theStack, (theState, theInput, theOutput))
    | READ -> (
        match theInput with
        | h :: t -> ([h] @ theStack, (theState, t, theOutput)))
    | WRITE -> (
        match theStack with
        | h :: t -> (t, (theState, theInput, theOutput @ [h])))
    | LD x -> ([theState x] @ theStack, (theState, theInput, theOutput))
    | ST x -> (
        match theStack with
        | h :: t -> (t, (Syntax.Expr.update x h theState, theInput, theOutput)));;

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval theConfig theProgram = List.fold_left evalStep theConfig theProgram

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

let rec compileExpr theExpression =
    match theExpression with
    | Syntax.Expr.Var x -> [LD x]
    | Syntax.Expr.Const n -> [CONST n]
    | Syntax.Expr.Binop (theOp leftOp rightOp) ->
        (compileExpr leftOp) @ (compileExpr rightOp) @ [BINOP theOp];;

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile theProgram =
    match theProgram with
    | Syntax.Stmt.Assign (x, e) -> (compileExpr e) @ [ST x]
    | Syntax.Stmt.Read x -> [READ; ST x]
    | Syntax.Stmt.Write e -> (compileExpr e) @ [WRITE]
    | Syntax.Stmt.Seq (s1, s2) -> (compile s1) @ (compile s2);;
