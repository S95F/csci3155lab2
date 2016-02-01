package jsy.student

object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._

  /*
   * CSCI 3155: Lab 2
   * <stfu2360>
   * 
   * Partner: <Alicia>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the '???' expression with  your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The ???
   * is a Scala expression that throws the exception scala.NotImplementedError.
   *
   */

  /* We represent a variable environment as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */

  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }

  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(true) => 1.0
      case B(false) => 0.0
      case S(s) => try s.toDouble catch { case _: Throwable => Double.NaN}
      case Undefined => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => {if(n == 0 | n.isNaN()) false else true}
      case S(s) => if( s == "" ) false else true
      case Undefined => false
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case Undefined => "undefined"
      case N(n) => n.toString
      case B(b) => b.toString
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)

    e match {
	  case Unary(Neg, e) => N((0-toNumber(eToVal(e))))
	  case Unary(Not, e) => B((!toBoolean(eToVal(e))))
	  case Binary(bop, e1, e2) => {
	  bop match{
		  case Plus =>{
			  (e1,e2) match {
				  case (S(_),_)|(_,S(_)) => {
					  S(toStr(eToVal(e1)) + toStr(eToVal(e2)))
					  }
				  case (_,_) => {
					  N(toNumber(eToVal(e1)) + toNumber(eToVal(e2)))
					}
				  }
		  }
		  case Minus =>{
			 (e1,e2) match {
				 case (S(_), _){
					 S(toStr(eToVal(e1)) - toStr(eToVal(e2)))
					 }
				 case (_,_){
					 N(toNumber(eToVal(e1)) - toNumber(eToVal(e2)))
					 }
				 } 
		  }
		  case Times =>{
			  N(toNumber(eToVal(e1)) * toNumber(eToVal(e2)))
		  }
		  case Div => {
			  N(toNumber(eToVal(e1)) / toNumber(eToVal(e2)))
		  }
		  case Eq => {
			  (e1, e2) match{
				  case ( Undefined , _ ) | ( _ , Undefined ) => {
						  B(false)
						  }
				  case (_, _) => {
						  B((toString(eToVal(e1)).equals(toString(eToVal(e2)))))
				  }
			}
		  }
		  case Ne => {
			  (e1, e2) match{
				  case ( Undefined , _ ) | ( _ , Undefined ) => {
						  B(false)
						  }
				  case (_, _) => {
						  B(!(toString(eToVal(e1)).equals(toString(eToVal(e2)))))
				  }
			}
		  }
		  case Lt => {
			  (e1, e2) match{
				  case ( Undefined , _ ) | ( _ , Undefined ) => {
					  B(false)
					  }
				  case (S(e1),S(e2)) => {
					  B(toString(eToVal(e1)).length() < toString(eToVal(e2)).length())
					  }
				  case (_,_) => {
					  B(toNumber(eToVal(e1)) < toNumber(eToVal(e2)))
					  }
				  }
			  }
		  case Le => {
			  (e1, e2) match{
				  case ( Undefined , _ ) | ( _ , Undefined ) => {
					  B(false)
					  }
				  case (S(e1),S(e2)) => {
					  B(toString(eToVal(e1)).length() <= toString(eToVal(e2)).length())
					  }
				  case (_,_) => {
					  B(toNumber(eToVal(e1)) <= toNumber(eToVal(e2)))
					  }
				  }
			  }
		  case Gt => {
			  (e1, e2) match{
				  case ( Undefined , _ ) | ( _ , Undefined ) => {
					  B(false)
					  }
				  case (S(e1),S(e2)) => {
					  B(toString(eToVal(e1)).length() > toString(eToVal(e2)).length())
					  }
				  case (_,_) => {
					  B(toNumber(eToVal(e1)) > toNumber(eToVal(e2)))
					  }
				  }
			  }
		  case Ge => {
			  (e1, e2) match{
				  case ( Undefined , _ ) | ( _ , Undefined ) => {
					  B(false)
					  }
				  case (S(e1),S(e2)) => {
					  B(toString(eToVal(e1)).length() >= toString(eToVal(e2)).length())
					  }
				  case (_,_) => {
					  B(toNumber(eToVal(e1)) >= toNumber(eToVal(e2)))
					  }
				  }
			  }
		}
	  }
      case Print(e1) => println(pretty(eToVal(e1))); Undefined

      case _ => ???
    }
  }

  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = eval(emp, e)

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

  /* Interface to run your interpreter from the command-line.  You can ignore what's below. */
  def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

     println(pretty(v))
  }

}
