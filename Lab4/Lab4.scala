package jsy.student

object Lab4 extends jsy.util.JsyApplication {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Will Christie>
   * 
   * Partner: <Amir Kashipazha>
   * Collaborators: <Ryan O'Connell>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
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
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match { //eliminate consecutive duplicates from list.
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => if (h1 == h2) {compressRec(t1)} else h1 :: compressRec(t1)
  } //if h1 == h2, recurse on t1 (without h1), otherwise, recurse including h1.
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match {
      case Nil => h :: Nil
      case h1 :: t1 => if (h == h1) acc else h :: acc // similar to above.
    }
  }
  
  def mapFirst[A](f: A => Option[A])(l: List[A]): List[A] = l match {
    case Nil => l // no matches, return list as is.
    case h :: t => f(h) match {
      case Some(x) => x :: t  // if we find a match, complete operation and leave everything else the same.
      case None => h :: mapFirst(f)(t) // if match not found, then recurse onward on remainder of the list.
    }
  }
  
  /* Search Trees */
  
  sealed abstract class Tree {
    def insert(n: Int): Tree = this match {
      case Empty => Node(Empty, n, Empty)
      case Node(l, d, r) => if (n < d) Node(l insert n, d, r) else Node(l, d, r insert n)
    } 
    
    def foldLeft[A](z: A)(f: (A, Int) => A): A = {
      def loop(acc: A, t: Tree): A = t match {
        case Empty => acc //return accumulator if tree/node does not have left child.
        case Node(l, d, r) => loop(f(loop(acc, l), d), r) //in order traverse left, accumulating result of traversal.
      }
      loop(z, this)
    }
    
    def pretty: String = {
      def p(acc: String, t: Tree, indent: Int): String = t match {
        case Empty => acc
        case Node(l, d, r) =>
          val spacer = " " * indent
          p("%s%d%n".format(spacer, d) + p(acc, l, indent + 2), r, indent + 2)
      } 
      p("", this, 0)
    }
  }
  case object Empty extends Tree
  case class Node(l: Tree, d: Int, r: Tree) extends Tree
  
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }
  
  def sum(t: Tree): Int = t.foldLeft(0){ (acc, d) => acc + d }
  
  def strictlyOrdered(t: Tree): Boolean = { // ensure data are in ascending order. covered in class.
    val (b, _) = t.foldLeft((true, None: Option[Int])) {
        case((true, None), current) => (true, Some(current))
        case((true, Some(left)), current) => (left < current, Some(current)) //check that L child is less than parent.
        case((false, _), _) => (false, None) //as soon as false, kill program.
    }
    b
  }
  

  /* Type Inference */

  type TEnv = Map[String, Typ]
  val emp: TEnv = Map()
  def get(env: TEnv, x: String): Typ = env(x)
  def extend(env: TEnv, x: String, t: Typ): TEnv = env + (x -> t)
  
  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if fields exists { case (_, t) => hasFunctionTyp(t) }=> true
    case _ => false
  }
  
  def typeInfer(env: TEnv, e: Expr): Typ = {
    // Some shortcuts for convenience
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => env(x)
      case ConstDecl(x, e1, e2) => typeInfer(extend(env, x, typ(e1)), e2)
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => typ(e1) match {
        case TNumber =>typ(e2) match {
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        case TString => typ(e2) match {
          case TString => TString
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary((Minus | Times | Div), e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }

      case Binary(Eq | Ne, e1, e2) => (typ(e1), typ(e2)) match {
        case (TFunction(params, tret),_) => err(typ(e1), e1)
        case (_,TFunction(params, tret)) => err(typ(e2), e2)
        case _ => if (typ(e1)==typ(e2)) TBool else err(typ(e2), e2)
      }
      case Binary(Lt | Le | Gt | Ge, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match {
          case TNumber => TBool
          case tgot => err(tgot, e2)
        }
        case TString => typ(e2) match {
          case TString => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)

      }
      case Binary(And | Or, e1, e2) => typ(e1) match {
        case TBool => typ(e2) match {
          case TBool => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Seq, e1, e2) => typ(e2)
      case If(e1, e2, e3) =>
        if (typ(e1) != TBool) err(typ(e1), e1)
        if (typ(e2) == typ(e3)) typ(e2) else err(typ(e2), e2)

      case Function(p, params, tann, e1) => { // REMEMBER THAT E1 IS THE EBODY OF THE FUNCTION.
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            extend(env, f, tprime)
          case (None, _) => env
          case _ => err(TUndefined, e1) //case for named function without a return value.
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1) {
          //extend env2 with list of params env1. params = tuple(string,type)
          case (newEnv, (paramName, paramType)) => extend(newEnv, paramName, paramType) //acc = current environment initially
        }
        // Match on whether the return type is specified.
        tann match {
          case None => TFunction(params, typeInfer(env2, e1)) //similar to val t1 = typeInfer(env2, e1)
          case Some(tret) =>
            if (TFunction(params, tret) != TFunction(params, typeInfer(env2, e1))) //check that params and tret are the same as what we look up in env2.
              err(TFunction(params, typeInfer(env2, e1)), e1)
            else TFunction(params, typeInfer(env2, e1)) //look up in env2 and return the type.
        }
      }
      case Call(e1, args) => typ(e1) match {
        case TFunction(params, tret) if params.length == args.length =>
          (params, args).zipped.foreach { //zipped params and args together. then do this for each.
            (p, a) => if (p._2 == typ(a)) (p,a) else err(p._2, a) //type of parameter is the same as the argument, then we are OK.
          }
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.map { case (x, y) => (x, typ(y)) }) //check the type of what is mapped to x.
      case GetField(e1, f) => typ(e1) match {
        case TObj(fields) => if (fields.contains(f)) fields(f) else err(typ(e1), e1) //check to see if the field we are accessing is there.
        case _ => err(typ(e1), e1)
      }
    }
  }

  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = { // same as in lab 3
    require(isValue(v1), "v1 in inequalityVal is not a value")
    require(isValue(v2), "v2 in inequalityVal is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => (bop: @unchecked) match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case (N(n1), N(n2)) => (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v), "Expr to substitute is not a value")
    
    def subst(e: Expr): Expr = substitute(e, v, x)
    
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
        /***** Cases from Lab 3 */ // same as in lab3
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (y == x) v else e
      case ConstDecl(y, e1, e2) => if (x == y) ConstDecl(y, subst(e1), e2) else ConstDecl(y, subst(e1), subst(e2))
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) =>
        val s = params.map((f: (String, Typ)) => f._1 == x)
        if (p == Some(x) || s.foldRight(false)(_ || _)) Function(p, params, tann, e1)
        else Function(p, params, tann, subst(e1))
      case Call(e1, args) => Call(subst(e1), args map subst) //call subst e1, e2, e3, etc...
        /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.mapValues(v => subst(v))) //perform subst on everything in object.
      case GetField(e1, f) => if(x != f) GetField(subst(e1), f) else e
    }
  }
  
  def step(e: Expr): Expr = {
    require(!isValue(e), "input Expr to step is a value")
    
    def stepIfNotValue(e: Expr): Option[Expr] = if (isValue(e)) None else Some(step(e))
    
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Unary(Neg, N(n1)) => N(- n1)
      case Unary(Not, B(b1)) => B(! b1)
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)
      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2)) => N(n1 / n2)
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2)=> B(inequalityVal(bop, v1, v2))
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)
      case Binary(And, B(b1), e2) => if (b1) e2 else B(false)
      case Binary(Or, B(b1), e2) => if (b1) B(true) else e2
      case If(v1, e2, e3) if isValue(v1) => v1 match {
        case B(true) => e2
        case B(false) => e3
      }
      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)
      case Call(v1, args) if isValue(v1) && (args forall isValue) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val e1p = (params, args).zipped.foldRight(e1){ //zipping all params together
              (p, acc)=> p match {
                case((name, _), value) => substitute(acc, value, name)
              } // apply via case expression to do unpacking and substitute in params one by one.
            }
            p match {
              case None => e1p
              case Some(x1) => substitute(e1p, v1, x1)
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. Make sure to replace the case _ => ???. */

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. Make sure to replace the case _ => ???. */
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop, e1, e2) => if (isValue(e1)) Binary(bop, e1, step(e2)) else Binary(bop, step(e1), e2)
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2) //step e1 to a value.
        /***** Cases needing adapting from Lab 3 */
      case Call(v1 @ Function(_, _, _, _), args) => Call(v1, mapFirst(stepIfNotValue)(args)) // mapfirst to step first non-value of args.
      case Call(e1, args) => Call(step(e1), args)
        /***** New cases for Lab 4. Make sure to replace the case _ => ???. */
      case Obj(fields) => { //map first used to access each field. if is not value, then step it. continue this until
        val map = mapFirst((field : (String, Expr)) => if (!isValue(field._2)) Some((field._1, step(field._2))) else None)(fields.toList)
        Obj(map.foldLeft(Map(): Map[String,Expr]) {
          (nfields, field) => nfields + (field._1 -> field._2) //._used to get the tuples of the fields.
        })
      }
      case GetField(obj, field) => obj match {
        case Obj(f) => f.get(field) match {
          case Some(x) => x // if the field is there.
          case None => throw new StuckError(e) // if x is not there. we can't do anything about it.
        }
        case e1 => GetField(step(e1), field) //otherwise step non values.
      }

      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information

  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  def iterateStep(e: Expr): Expr = {
    require(closed(e), "input Expr to interateStep is not closed")
    def loop(e: Expr, n: Int): Expr = {
      if (debug) { println("Step %s: %s".format(n, e)) }
      if (isValue(e)) e else loop(step(e), n + 1)
    }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val v = loop(e, 0)
    if (debug) {
      println("Value: " + v)
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(Parser.parse(s))

  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val e1 =
      handle(None: Option[Expr]) {Some{
        Parser.parseFile(file)
      }} getOrElse {
        return
      }

    val welltyped = handle(false) {
      println("# Type checking ...")
      val t = inferType(e1)
      println("## " + pretty(t))
      true
    }
    if (!welltyped) return

    handle() {
      println("# Stepping ...")
      def loop(e: Expr, n: Int): Expr = {
        println("## %4d: %s".format(n, e))
        if (isValue(e)) e else loop(Lab4.step(e), n + 1)
      }
      val v1 = loop(e1, 0)
      println(pretty(v1))
    }
  }

}

