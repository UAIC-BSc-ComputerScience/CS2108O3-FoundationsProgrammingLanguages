module TEST2-SYNTAX
  syntax AExp ::= Id | Int | AExp "+" AExp [left, strict]
  syntax Block ::= "{" "}"
  	         | "{" Stmt "}"
  syntax Stmt ::= "var" Ids
  	      	| Block
                > Id ":=" AExp [strict(2)]
		> Stmt ";" Stmt [left]
  syntax Ids ::= List{Id,","}
endmodule

module TEST2
  imports TEST2-SYNTAX

  configuration <T>
   		  <k> $PGM:Stmt </k>
		  <env> .Map </env>
		  <store> .Map </store>
		</T>

  syntax KResult ::= Int
  // stmt sequence
  rule S1 ; S2 => S1 ~> S2
  // var decl
  rule <k> var (X,Xs => Xs) ...</k>
       <env> Rho:Map => Rho[X <- !L:Int] </env>
       <store> Sigma:Map (. => !L |-> 0) </store> 
  rule var .Ids => .
  // plus
  rule I1:Int + I2:Int => I1 +Int I2
  // variable lookup
  rule <k> X => V:Int ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V ...</store>
  // assignment
  rule <k> X := V:Int => . ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> (_ => V) ...</store>
  // blocks
  rule { } => .
  rule <k> { S } => S ~> restore(Rho) ...</k>
       <env> Rho:Map </env>
  // restore
  syntax KItem ::= "restore" "(" Map ")"
  rule <k> restore(Rho:Map) => . ...</k>
       <env> _ => Rho </env>       
endmodule