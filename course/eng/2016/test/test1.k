module TEST1-SYNTAX
  syntax AExp ::= Id | Int
  	        | AExp "*" AExp [left, strict]
		> AExp "+" AExp [left, strict]
  syntax Stmt ::= "var" Ids
  	      	| "skip"
                > Id ":=" AExp [strict(2)]
		> "if" AExp "then" Stmt "else" Stmt [strict(1)]
		| "if" AExp "then" Stmt  [strict(1), prefer]
		> Stmt ";" Stmt [left]
  syntax Ids ::= List{Id,","}
endmodule

module TEST1
  imports TEST1-SYNTAX

  configuration <T>
   		  <k> $PGM:Stmt </k>
		  <state> .Map </state>
		</T>

  syntax KResult ::= Int
  // stmt sequence
  rule S1 ; S2 => S1 ~> S2
  // var decl
  rule <k> var (X,Xs => Xs) ...</k>
       <state> Rho:Map (. => X |-> 0) </state> requires notBool(X in keys(Rho))
  rule var .Ids => .
  // exp
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int * I2:Int => I1 *Int I2
  // variable lookup
  rule <k> X => V:Int ...</k>
       <state>... X |-> V ...</state>
  // assignment
  rule <k> X := V:Int => . ...</k>
       <state>... X |-> (_ => V) ...</state>
  // skip
  rule skip => . 
  // if statements
  rule if I:Int then S else _ => S requires I >Int 0
  rule if 0 then _ else S => S
  rule if I:Int then S => if I then S else skip
endmodule