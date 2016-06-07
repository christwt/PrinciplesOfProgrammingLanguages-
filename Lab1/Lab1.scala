package jsy.student

object Lab1 extends jsy.util.JsyApplication {

  import jsy.lab1.Parser
  import jsy.lab1.ast._

  /*
   * CSCI 3155: Lab 1
   * <Your Name>
   *
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */

  /*
   * Example with a Unit Test
   *
   * A convenient, quick-and-dirty way to experiment, especially with small code
   * fragments, is to use the interactive Scala interpreter.
   *
   * To start the interactive Scala interpreter in IntelliJ, select Run Scala Console
   * from the Tools menu or the right-click menu for this file.
   *
   * To run a selection in the interpreter, highlight the code of interest
   * and select Send Selection to Scala Console from the right-click menu
   * or type Ctrl+Shift+X.
   *
   * Highlight the next few lines below to try it out.  The assertion passes, so
   * it appears that nothing happens.  You can uncomment the "bad test specification"
   * and see that a failed assert throws an exception.
   *
   * You can try calling 'plus' with some arguments, for example, plus(1,2).  You
   * should get a result something like 'res0: Int = 3'.
   *
   * As an alternative, the testPlus2 function takes an argument that has the form
   * of a plus function, so we can try it with different implementations.  For example,
   * uncomment the "testPlus2(badplus)" line, and you will see an assertion failure.
   *
   * While writing such testing snippets are convenient, it is not ideal.  For example,
   * the 'testPlus1()' call is run whenever this object is loaded, so in practice,
   * it should probably be deleted for "release".  A more robust way to maintain
   * unit tests is in a separate file.  For us, we use the convention of writing
   * tests in a file called LabXSpec.scala (i.e., Lab1Spec.scala for Lab 1).
   *
   * IntelliJ has another way to interactively run Scala expressions via Scala Worksheets.
   * A Scala Worksheet (e.g., Lab1Worksheet.sc) is code evaluated in the context of the
   * project with results for each expression shown inline.
   *
   */

  def plus(x: Int, y: Int): Int = x + y

  def testPlus1() {
    assert(plus(1, 1) == 2)
    //assert(plus(1,1) == 3) // bad test specification
  }

  testPlus1()

  def badplus(x: Int, y: Int): Int = x - y

  def testPlus2(plus: (Int, Int) => Int) {
    assert(plus(1, 1) == 2)
  }

  //testPlus2(badplus)

  /* Exercises */

  def abs(n: Double): Double = if (n < 0) -n else n
  // if n < 0 then return -n
  // otherwise return positive n.

  def xor(a: Boolean, b: Boolean): Boolean = if (a != b) true else false
  // if a == true and b == false: return true
  // if a == false and b == true: return true
  // if a == b: return false

  def repeat(s: String, n: Int): String = {
    require(n >= 0)
    if (n == 0) ""
    else s + repeat(s, n - 1)
  }
  // throw exception if negative n is used.
  // base case: n==0 will return an empty string.
  // inductive step: return string w/ recursive call.


  def sqrtStep(c: Double, xn: Double): Double = xn - ((xn * xn) - c) / (2 * xn)
  //use formula in sheet to compute xn+1

  def sqrtN(c: Double, x0: Double, n: Int): Double = {
    require(c >= 0 && n >=0)
    def improve(guess: Double, n: Int): Double = {
      if (n == 0) guess
      else improve(sqrtStep(c, guess), n-1)
    }
    improve(x0, n)
    //iterative attempt possible with a while loop, prefer to use recursion as above.
    //throw exception if c or n are negative.
    //base case: if n == 0, take the current estimation.
    //inductive step: recurse with improve function, using sqrtStep to get Xn+1
  }

  def sqrtErr(c: Double, x0: Double, epsilon: Double): Double = {
    require(c > 0 && epsilon > 0)
    def improve(guess: Double): Double = {
      if (abs(guess*guess-c) <= epsilon) guess
      else improve(sqrtStep(c,guess))
    }
    improve(x0)
}
  //utilize first guess and compare with equation.
  //base case: when abs(x0*x0) - c) < epsilon, if true then return our guess.
  //inductive step: call improve again with sqrtStep to get Xn+1.

  def sqrt(c: Double): Double = {
    require(c >= 0)
    if (c == 0) 0 else sqrtErr(c, 1.0, 0.0001)
  }

  /* Search Tree */

  sealed abstract class SearchTree
  case object Empty extends SearchTree
  case class Node(l: SearchTree, d: Int, r: SearchTree) extends SearchTree


  /* def height(t: SEarchTree): Int = t match{
      case Empty => 0
      case Node(l,-,r)=> 1 + (height(l) max height(r))
   */
  def repOk(t: SearchTree): Boolean = {
    def check(t: SearchTree, min: Int, max: Int): Boolean = t match {
      case Empty => true // base case: end of the tree.
      case Node(l, d, r) =>
          if (d < min || d > max) false
          else check(l, min, d) && check(r, d, max)
    }
    check(t, Int.MinValue, Int.MaxValue)
    //return true if tree is empty.
    //return false if d is outside the min/max constraints.
    //else recurse through subtrees, tightening min/max constraints until node is reached.
  }

  def insert(t: SearchTree, n: Int): SearchTree = t match {
    case Empty => Node(Empty, n, Empty) // base case: insert with empty children.
    case Node(l, d, r) =>
      if (n < d) Node(insert(l, n), d, r) //go left if n < d.
      else Node(l, d, insert(r, n)) // go right if n > d
    //if Empty: then add n at root.
    //if n < d recurse left until insertion.
    //if n > d recurse right until insertion.
  }

  def deleteMin(t: SearchTree): (SearchTree, Int) = {
    require(t != Empty)
    (t: @unchecked) match {
      case Node(Empty, d, r) => (r, d) // if left child empty, return right node.
      case Node(Empty, d, Empty) => (Empty, d) // if no children, return node as is.
      case Node(l, d, r) => // if 2 children, then continue going left.
        val (l1, m) = deleteMin(l)
        (Node(l1,d,r), m) //return final leftmost child.
    //throw exception if the tree is empty
    //case if L child is empty: return the right node.
    //case if tree has no children. return the node.
    //final case: if node has 2 children. call delete min(l) to continue going left.
    //then return the final left child that was deleted.
    }
  }

  def delete(t: SearchTree, n: Int): SearchTree = t match{
    case Empty => t
    case Node(Empty, d, Empty) if n == d => Empty
    case Node(Empty, d, r) if n == d  => r
    case Node(l, d, Empty) if n == d => l
    case Node(l,d,r) =>
      if (n == d){
        val (r1, v) = deleteMin(r)
        Node(l, v, r1)
      }
      else if (d > n){
        Node(delete(l, n), d, r)
      } else {
        Node(l, d, delete(r, n))
      }
    //case1: if node as no children. return Empty.
    //case2: if node has L child only.
    //case3: if node has R child only.
    //case4: if node has 2 children.
      // swap with min and delete min
      // if we aren't there yet then recurse right or left until we find it.
  }

  /* JavaScripty */

  def eval(e: Expr): Double = e match {
    case N(n) => n
    case Binary(Plus,e1,e2) => eval(e1) + eval(e2)
    case Binary(Minus,e1,e2) => eval(e1) - eval(e2)
    case Binary(Times,e1,e2) => eval(e1) * eval(e2)
    case Binary(Div,e1,e2) => eval(e1) / eval(e2)
    case Unary(Neg,e1) => -eval(e1)
    case _ => throw new UnsupportedOperationException
  }

 // Interface to run your interpreter from a string.  This is convenient
 // for unit testing.
 def eval(s: String): Double = eval(Parser.parse(s))



 /* Interface to run your interpreter from the command-line.  You can ignore the code below. */

 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println(s"\nExpression AST:\n  ${expr}")
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

    println(v)
  }

}