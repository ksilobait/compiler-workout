(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let boolToInt b = if b then 1 else 0;;

    let intToBool i = i != 0;;
    
    let processBinop theOp leftOp rightOp =
        match theOp with
        | "+" -> leftOp + rightOp
        | "-" -> leftOp - rightOp
        | "*" -> leftOp * rightOp
        | "/" -> leftOp / rightOp
        | "%" -> leftOp mod rightOp
        | "==" -> boolToInt (leftOp == rightOp)
        | "!=" -> boolToInt (leftOp != rightOp)
        | "<" -> boolToInt (leftOp < rightOp)
        | "<=" -> boolToInt (leftOp <= rightOp)
        | ">" -> boolToInt (leftOp > rightOp)
        | ">=" -> boolToInt (leftOp >= rightOp)
        | "&&" -> boolToInt (intToBool leftOp && intToBool rightOp)
        | "!!" -> boolToInt (intToBool leftOp || intToBool rightOp);;
    
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval theState theExpr = (
        match theExpr with
        | Const theConst -> theConst
        | Var theVariable -> theState theVariable
        | Binop (theOp, leftOp, rightOp) ->
            processBinop theOp (eval theState leftOp) (eval theState rightOp));;

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (theState, theInput, theOutput) theStatement = 
        match theStatement with
        | Read x -> (
            match theInput with
            | h::t -> (Expr.update x h theState, t, theOutput))
        | Write e ->(theState, theInput, theOutput @ [Expr.eval theState e])
        | Assign (x, e) -> (Expr.update x (Expr.eval theState e) theState, theInput, theOutput)
        | Seq (s1, s2) -> (
            let eval (theState, theInput, theOutput) s1 = cc in
            eval cc s2);;
                                                         
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
