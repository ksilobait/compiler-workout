(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
    
    let parseBinop theOp = ostap(- $(theOp)), (fun leftOp rightOp -> Binop (theOp, leftOp, rightOp));;

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
        expr:
            !(Ostap.Util.expr
                (fun x -> x)
                (Array.map
                (fun (theAssociativity, theOperations) -> theAssociativity, List.map parseBinop theOperations)
                    [|
                        `Lefta, ["!!"];
                        `Lefta, ["&&"];
                        `Nona, [">="; ">"; "<="; "<"; "=="; "!="];
                        `Lefta, ["+"; "-"];
                        `Lefta, ["*"; "/"; "%"];
                    |]
                )
                primary
            );
        primary: x:IDENT {Var x} | n:DECIMAL {Const n} | -"(" expr -")"
    );;
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | RepeatUntil of t * Expr.t with show
                                                                    
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
        | Seq (s1, s2) ->
            let cc = eval (theState, theInput, theOutput) s1 in
                eval cc s2
        | Skip -> (theState, theInput, theOutput)
        | If (e, s1, s2) ->
            let result = Expr.eval theState e in
            if result = 0 then
                eval (theState, theInput, theOutput) s2
            else
                eval (theState, theInput, theOutput) s1
        | While (e, s) ->
            let result = Expr.eval theState e in
            if result = 0 then
                (theState, theInput, theOutput)
            else
                let (theState', theInput', theOutput') = eval (theState, theInput, theOutput) s in
                eval (theState', theInput', theOutput') theStatement
        | RepeatUntil (s, e) ->
            let (theState', theInput', theOutput') = eval (theState, theInput, theOutput) s in
            let result = Expr.eval theState' e in
            if result = 0 then
                eval (theState', theInput', theOutput') theStatement
            else
                (theState', theInput', theOutput');;
                
        
    
    (* Statement parser *)
    ostap (
        stmt: "read" "(" x:IDENT ")" {Read x}
            | "write" "(" theExpr:!(Expr.expr) ")" {Write theExpr}
            | x:IDENT ":=" theExpr:!(Expr.expr) {Assign (x, theExpr)}
            | "if" theExpr: !(Expr.expr) "then"
                then_body: !(parse)
                elif_body: (%"elif" !(Expr.expr) %"then" !(parse))*
                els: (%"else" !(parse))?
                "fi"
                {
                    let else_body =
                        match els with
                        | Some x -> x
                        | _ -> Skip
                    in
                    let else_body' = List.fold_right (fun (theExpr', then') els' -> If (theExpr', then', els')) elif_body else_body in
                    If (theExpr, then_body, else_body')
                }
            | "while" theExpr:!(Expr.expr) "do" body:!(parse) "od" {While (theExpr, body)}
            | "for" init:!(parse) "," theExpr:!(Expr.expr) "," step:!(parse) "do" body:!(parse) "od"
                {
                    Seq (init, While (theExpr, Seq (body, step)))
                }
            | "repeat" body:!(parse) "until" theExpr:!(Expr.expr)
                { 
                    RepeatUntil (body, theExpr)
                }
            | "skip" {Skip};
        
        parse: h:stmt ";" t:parse {Seq (h, t)} | stmt
    );;
    
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
