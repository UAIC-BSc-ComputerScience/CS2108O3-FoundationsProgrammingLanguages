module TEST3-SYNTAX
  syntax AExp ::= Id | Int
  	        | AExp "*" AExp [left, strict]
		> AExp "+" AExp [left, strict]
  syntax Stmt ::= "int" Ids
                > Id "<-" AExp [strict(2)]
		> "while" AExp "do" "{" Stmt "}"  
		> Stmt ";" Stmt [left]
  syntax Ids ::= List{Id,","}
endmodule

module TEST3
  imports TEST3-SYNTAX

  configuration <T>
   		  <k> $PGM:Stmt </k>
		  <state> .Map </state>
		</T>

  syntax KResult ::= Int
  // stmt sequence
  rule S1 ; S2 => S1 ~> S2
  // var decl
  rule <k> int (X,Xs => Xs) ...</k>
       <state> Rho:Map (. => X |-> 0) </state> requires notBool(X in keys(Rho))
  rule int .Ids => .
  // exp
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int * I2:Int => I1 *Int I2
  // variable lookup
  rule <k> X => V:Int ...</k>
       <state>... X |-> V ...</state>
  // assignment
  rule <k> X <- V:Int => . ...</k>
       <state>... X |-> (_ => V) ...</state>
  // helper
  syntax KItem ::= "eval" "(" AExp "," Stmt ")" [strict(1)]
  rule eval(0,S) ~> while E do { S } => .
  rule eval(I:Int, S) => S requires I =/=Int 0
  // while statement
  rule while E do { S } => eval(E,S) ~> while E do { S } 

endmodule