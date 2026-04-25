module TEST4-SYNTAX
  syntax AExp ::= Id | Int | String
  syntax Block ::= "{" Stmt "}"
  syntax Stmt ::= "var" Ids
  	      	| Block
		| "print" "(" AExps ")" [strict(1)]
                > Id ":=" AExp [strict(2)]
		> Stmt ";" Stmt [left]
  syntax Ids ::= List{Id,","}
  syntax AExps ::= List{AExp, ","} [strict]
endmodule

module TEST4
  imports TEST4-SYNTAX

  configuration <T>
   		  <k> $PGM:Stmt </k>
		  <env> .Map </env>
		  <store> .Map </store>
		  <out stream="stdout"> .List </out>
		</T>

  // results
  syntax Val ::= Int | String
  syntax Vals ::= List{Val, ","}
  syntax KResult ::= Val | Vals

  // stmt sequence
  rule S1 ; S2 => S1 ~> S2
  // var decl
  rule <k> var (X,Xs => Xs) ...</k>
       <env> Rho:Map => Rho[X <- !L:Int] </env>
       <store> Sigma:Map (. => !L |-> 0) </store> 
  rule var .Ids => .
  // variable lookup
  rule <k> X => V:Int ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V ...</store>
  // assignment
  rule <k> X := V:Int => . ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> (_ => V) ...</store>
  // blocks
  rule <k> { S } => S ~> restore(Rho) ...</k>
       <env> Rho:Map </env>
  // restore
  syntax KItem ::= "restore" "(" Map ")"
  rule <k> restore(Rho:Map) => . ...</k>
       <env> _ => Rho </env>

  // enable the use of Vals in the same places where AExps may appear
  syntax AExps ::= Vals
  syntax AExp ::= Val
  // print
  rule <k> print (V:Val, Vs => Vs) ...</k>
       <out>... . => ListItem(V) </out>
  rule print(.Vals) => .
endmodule