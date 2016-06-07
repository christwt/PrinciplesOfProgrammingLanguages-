package jsy.student

object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._

  /*
   * CSCI 3155: Lab 2
   * Will Christie
   * IdentiKey: christwt
   * 
   * Partner: Ryan O'Connell
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
      case S(s) => try s.toDouble catch { case _: Throwable => Double.NaN }
      case Undefined => Double.NaN
    }
    // if number, return the number
    // if boolean true, return 1.0
    // if boolean false, return 0.0
    // if string, attempt toDouble method, if failed will catch exception and thrown NaN.
    // if undefined, return NaN
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) if (n compare 0.0) == 0 || (n compare -0.0) == 0 || n.isNaN => false
      case N(_) => true
      case S("") => false
      case S(_) => true
      case Undefined => false

     //if Boolean, return boolean.
     //if number, return true as long as number != 0 && .isNaN.
     //if string, as long as string is not empty, return true.
     //if undefined, return false
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case Undefined => "undefined"
      case B(b) => b.toString
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString
    }
    // if string, return string.
    // if undefined, return undefined.
    // if Boolean(t) return "true"
    // if Boolean(f) return "false"
    // if number:
      // if whole number, then format with .0
      // if double already, then format with .toString method.
  }
  /*
   Created helper function to implement inequality operations
   on values including Lt, Le, Gt, Ge
   inequalityOps has 2 cases: string vs number
   will either use string or attempt to convert to number to evaluate
   the inequality.
  */
  def inequalityOps(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2))  => (bop: @unchecked) match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case _ => val (n1, n2) = (toNumber(v1), toNumber(v2))
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    //eToVal: already given
    def eToVal(e: Expr): Expr = eval(env, e)
    //eToNum: perform conversion of expression to Double
    def eToNum(e: Expr): Double = toNumber(eval(env, e))
    //eToBool: perform conversion of expression to Boolean
    def eToBool(e: Expr): Boolean = toBoolean(eval(env, e))

    e match {

      /* Base Cases */
      case _ if isValue(e) => e
      case Var(x) => eToVal(get(env, x))
      /* Inductive Cases */
        //print: already provided.
      case Print(e1) => println(pretty(eToVal(e1))); Undefined
      //Unary Negation
        //Neg
      case Unary(Neg, e1) => N(- eToNum(e1))
        //Not
      case Unary(Not, e1) => B(! eToBool(e1))
      //Binary operations
        //Plus
      case Binary(Plus, e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (S(s1), v2) => S(s1 + toStr(v2))
        case (v1, S(s2)) => S(toStr(v1) + s2)
        //accounts for strange edge cases including Boolean by casting toNumber.
        case (v1, v2) => N(toNumber(v1) + toNumber(v2))
      }
        //Minus
      case Binary(Minus, e1, e2) => N(eToNum(e1) - eToNum(e2))
        //Times
      case Binary(Times, e1, e2) => N(eToNum(e1) * eToNum(e2))
        //Division
      case Binary(Div, e1, e2) => N(eToNum(e1) / eToNum(e2))
        //Equals "===" Types need to be the same. otherwise if differing type will return false.
      case Binary(Eq, e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (S(s1), S(s2)) => B(s1 == s2)
        case (N(n1), N(n2)) => B(n1 == n2)
        case (B(b1), B(b2)) => B(b1 == b2)
        case (Undefined, Undefined) => B(true)
        case (_, _) => B(false)
      }
        //Negation
      case Binary(Ne, e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (S(s1), S(s2)) => B(s1 != s2)
        case (N(n1), N(n2)) => B(n1 != n2)
        case (B(b1), B(b2)) => B(b1 != b2)
        case (Undefined, Undefined) => B(false)
        case (_, _) => B(true)
      }
        //Inequality Operators: see helper function inequalityOps above
      case Binary(bop @ (Lt|Le|Gt|Ge), e1, e2) => B(inequalityOps(bop, eToVal(e1), eToVal(e2)))
        //And
      case Binary(And, e1, e2) =>
        val v1 = eToVal(e1)
        if (toBoolean(v1)) eToVal(e2) else v1
      case Binary(Or, e1, e2) =>
        val v1 = eToVal(e1)
        if (toBoolean(v1)) v1 else eToVal (e2)
        //Sequence
      case Binary(seq, e1, e2) => eToVal(e1); eToVal(e2)
        //If
      case If(e1, e2, e3) => if (eToBool(e1)) eToVal(e2) else eToVal(e3)
        //Constant declaration
      case ConstDecl(x, e1, e2) => eval(extend(env, x, eToVal(e1)), e2)
        
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
