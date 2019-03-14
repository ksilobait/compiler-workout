open GT       
open Language
       
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

let evalStep (theStack, (theState, theInput, theOutput)) theProgram =
    match theProgram with
    | BINOP op -> (
        match theStack with
        | y :: x :: t -> ([Language.Expr.processBinop op x y] @ t, (theState, theInput, theOutput)))
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
        | h :: t -> (t, (Language.Expr.update x h theState, theInput, theOutput)));;

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)                         
let rec eval theConfig theProgram = List.fold_left evalStep theConfig theProgram

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
