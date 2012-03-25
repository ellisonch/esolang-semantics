kmod BF is
	/* \par{This is a formal semantics for the turing complete language ``brainfuck''.  Brainfuck was designed by Urban M\"uller in 1993.  More information can be found at \url{http://en.wikipedia.org/wiki/Brainfuck}.}  Some comments below are adapted from the Wikipedia article.
	
	\par{K formal semantics for BF written by Chucky Ellison (\href{mailto:celliso2@illinois.edu}{celliso2@illinois.edu}).  It has been translated from the ``fully labeled'' style to the syntactic style, but the tests need to be updated in order to run.}
	
	/
	*/
	including K
	
// Syntax
	syntax CellLabel ::= memory
	syntax CellLabel ::= output
	syntax CellLabel ::= result
	syntax CellLabel ::= input
	syntax CellLabel ::= k

	/*@ We use an abstract syntax in this formal semantics.  The mapping from concrete to abstract syntax is given by the following chart:
	
\begin{tabular}{@{}ll@{}}
\toprule
Concrete	& Abstract\\
\midrule
\texttt{+}	& \texttt{Increase}\\
\texttt{-}	& \texttt{Decrease}\\
\texttt{>}	& \texttt{GoRight}\\
\texttt{<}	& \texttt{GoLeft}\\
\texttt{\[}	& \multirow{2}{*}{\texttt{While}}\\
\texttt{\]}	&\\
\texttt{.}	& \texttt{Print}\\
\texttt{,}	& \texttt{Read}\\
\bottomrule
\end{tabular}

Note: the \texttt{\[} and \texttt{\]} commands of BF are assumed to be matching, and are represented by a single ``While'' construct.

*/
	// comments from http://en.wikipedia.org/wiki/Brainfuck
	syntax KLabel ::= `Seq
	syntax K ::= `GoRight
	syntax K ::= `GoLeft
	syntax K ::= `Increase
	syntax K ::= `Decrease
	syntax K ::= `Print
	syntax K ::= `Read
	syntax KLabel ::= `While
	
// Semantics
	syntax K ::= sentinel
	syntax Bag ::= eval( K )
	syntax Bag ::= eval-inp( K , K )
	syntax KResult ::= #Int
	syntax KResult ::= #String
	
	configuration 
		< T >
			< k > K:K </ k >
			< memory > L:List </ memory >
			< output > K:K </ output >
			< input > K:K </ input >
		</ T >  
		< result > K:K </ result > 
		
	rule [Start]: eval(K:K) => eval-inp(K:K, "") [structural]
		
	rule [Start-With-Input]: 
		eval-inp(K:K, K':K) => 
		< T >
			< k > K:K </ k >
			< memory > ListItem(sentinel) </ memory >
			< output > "" </ output >
			< input > K':K </ input >
		</ T >
		[structural]

	rule [Finish]: 
		< T > ?:Bag < k > .K </ k > < output > K:K </ output > </ T > 
			=> < result > K:K </ result >
		[structural]
		
	/*@ We use a sentinel to denote the edge of memory, and automatically create more memory when it is reached, */
	rule
		< memory > (.List => ListItem(0)) ListItem(sentinel) ...</ memory > 
		[structural]
	
	/*@ This rule simply turns sequenced commands into the first command followed by the rest, */
	rule [Sequence]: 
		Seq(K1:K,, K2:K) => K1:K ~> K2:K
		[structural]

	/*@ \texttt{Increase}: increment (increase by one) the byte at the data pointer. */
	rule [Increase]: 
		< k > Increase => .K ...</ k >
		< memory > ListItem((I:#Int => (I:#Int +Int 1))) ...</ memory > 
	/*@ \texttt{Decrease}: decrement (decrease by one) the byte at the data pointer. */
	rule [Decrease]: 
		< k > Decrease => .K ...</ k >
		< memory > ListItem((I:#Int => (I:#Int -Int 1))) ...</ memory > 

	/*@ \texttt{GoRight}: increment the data pointer (to point to the next cell to the right).  Note that the ``data pointer'' is represented by whatever is left-most in the memory cell.  Thus, to move the pointer right, we simply roll the contents of the cell to the left.
	*/
	rule [GoRight]: 
		< k > GoRight => .K ...</ k > 
		< memory > (Li:ListItem => .List) L:List (.List => Li:ListItem) </ memory > 
	/*@ \texttt{GoLeft}: decrement the data pointer (to point to the next cell to the left). */
	rule [GoLeft]: 
		< k > GoLeft => .K ...</ k > 
		< memory > (.List => Li:ListItem) L:List (Li:ListItem => .List) </ memory > 
	
	/*@ \texttt{While}: if the byte at the data pointer is zero, then instead of moving the instruction pointer forward to the next command, jump it past the end of the loop.  If the byte at the data pointer is nonzero, then instead of moving the instruction pointer forward to the next command, enter the loop.
	*/
	rule [WhileNZ-NZ]: 
		< k > While(K:K) => K:K ~> While(K:K) ...</ k > 
		< memory > ListItem(I:#Int) ...</ memory > 
		when I:#Int =/=Bool 0
	rule [WhileNZ-Z]: 
		< k > While(K:K) => .K ...</ k >
		< memory > ListItem(0) ...</ memory > 
	
	/*@ \texttt{Print}: output the value of the byte at the data pointer. */
	rule [Output]: 
		< k > Print => .K ...</ k > 
		< memory > ListItem(I:K) ...</ memory > 
		< output > S:#String => S:#String +String charString(eightbit(I:K)) </ output > 
	/*@ \texttt{Read}: accept one byte of input, storing its value in the byte at the data pointer.
	*/
	rule [Input]: 
		< k > Read => .K ...</ k >
		< memory > ListItem((I:#Int => charToAscii(firstChar(Input:K)))) ...</ memory > 
		< input > Input:K => butFirstChar(Input:K) </ input > 
		 
		
	/*@ The rest of the definition is simply helper functions. */
	syntax #Nat ::= eightbit "(" K ")"
	define
		eightbit(I:#Int) 
		=> (((I:#Int %Int 256) +Int 256) %Int 256)
		[structural]
		
	syntax K ::= firstChar "(" K ")"
	syntax K ::= butFirstChar "(" K ")"
	syntax K ::= charToAscii "(" K ")"
	
	define [firstChar]:
		firstChar(S:#String) => substrString(S:#String, 0, 1)
		[structural]
	define [charToAscii]: 
		charToAscii(C:#Char) => asciiString(C:#Char)
		[structural]
	define [butFirstChar]: 
		butFirstChar(S:#String) => substrString(S:#String, 1, lengthString(S:#String))
		[structural]
	// end helper functions
endkm

