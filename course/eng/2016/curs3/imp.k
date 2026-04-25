module IMP-SYNTAX
  syntax AExp ::= Int | Id
  	        | AExp "/" AExp [left, strict]
		> AExp "+" AExp [left, strict]
		| "(" AExp ")"  [bracket]

  syntax BExp ::= Bool
  	        | "!" BExp       [strict]
		| BExp "&&" BExp [strict(1)]
		| AExp "<=" AExp [strict]
		| "(" BExp ")"   [bracket]

  syntax Block ::= "{" "}"
  	 	  | "{" Stmt "}"

  syntax Stmt ::= Block
  	        | Id "=" AExp ";"			[strict(2)]
		| "if" "(" BExp ")" Stmt "else" Stmt    [strict(1)]
		| "while" "(" BExp ")" Stmt
		> Stmt Stmt				[left]

  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id, ","}
endmodule

module IMP
  imports IMP-SYNTAX

  configuration <T>
		  <k> $PGM:Pgm </k>
		  <env> .Map </env>
		</T>

  syntax KResult ::= Int | Bool

  // var declarations
  rule <k> int (X, Xs => Xs) ; S </k>
       <env> Rho:Map (. => (X |-> 0)) </env> requires notBool(X in keys(Rho))
  rule (int .Ids ; S) => S

  // AExp
  rule I1:Int + I2:Int => I1 +Int I2 
  rule I1:Int / I2:Int => I1 /Int I2 requires I2 =/=Int 0

  // BExp
  rule ! false => true
  rule ! true  => false
  rule true  && B => B
  rule false && _ => false
  rule I1:Int <= I2:Int => I1 <=Int I2
  

  // Sequences
  rule S1:Stmt S2:Stmt => S1 ~> S2

  // Assignment
  rule <k> (X = V:Int ; => .) ...</k>
       <env>... X |-> (_ => V) ...</env>

  // if
  rule if (true)  S else _ => S
  rule if (false) _ else S => S

  // lookup
  rule <k> (X => V) ...</k>
       <env>... X |-> V:Int ...</env>

  // Blocks
  rule { } => .
  rule { S:Stmt } => S 

  // while: loop unrolling
  rule while (B) S => if (B) { S while (B) S } else { }
  
  
endmodule
