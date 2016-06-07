package jsy.student

object Lab5 extends jsy.util.JsyApplication {
  import jsy.lab5.ast._
  import jsy.lab5._
  import jsy.util.DoWith
  import jsy.util.DoWith._

  /*
   * CSCI 3155: Lab 5
   * <Will Christie>
   *
   * Partner: <---->
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

  /*** Exercise with DoWith ***/

  def fresh: DoWith[Int,String] = doget flatMap { i =>
    val xp = "x" + i
    doput(i + 1) map { _ => xp }
  }

  def rename(env: Map[String, String], e: Expr): DoWith[Int,Expr] = {
    def ren(e: Expr): DoWith[Int,Expr] = rename(env, e)
    e match {
      case N(_) => doreturn(e)
      case Binary(Plus, e1, e2) => ren(e1) flatMap {
        case e1p => ren(e2) map {
          case e2p => Binary(Plus, e1p, e2p)
        }
      }
      case Var(x) => doreturn(Var(env(x)))
      case Decl(MConst, x, e1, e2) => fresh flatMap {
        case xp:String => ren(e1) flatMap {
          case e1p: Expr => {
            val envp = env + (x -> xp)
            rename(envp, e2) map {
              case e2p: Expr => Decl(MConst, xp, e1p, e2p)
            }
          }
        }
      }
      /* For this exercise, no need to implement any more cases than the ones above.
       * Leave the following default case. */
      case _ => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  def rename(e: Expr): Expr = {
    val (_, r) = rename(Map.empty, e)(0)
    r
  }

  def rename(s: String): Expr = rename(Parser.parse(s))

  /*** Helper: mapFirst to DoWith ***/

  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](f: A => Option[DoWith[W,A]])(l: List[A]): DoWith[W,List[A]] = l match {
    case Nil => doreturn(Nil)
    case h :: t => f(h) match {
      case None => mapFirstWith(f)(t) map { tp => h::tp }
      case Some(x) => x map { (hp:A) => hp::t: List[A] }
    }
  }

  /*** Casting ***/

  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
    /***** Make sure to replace the case _ => ???. */
    case (_,_) if (t1 == t2) => true
    case (TNull,TObj(_)) => true
    case (TObj(fields1), TObj(fields2)) => {fields1.foldLeft(true)((acc, e1) => acc && fields2.getOrElse(e1._1,TUndefined) == e1._2) ||
      fields2.foldLeft(true)((acc, e1) => acc && fields1.getOrElse(e1._1,TUndefined) == e1._2)
    }
    /***** Cases for the extra credit. Do not attempt until the rest of the assignment is complete. */
    case (TInterface(tvar, t1p), _) => ??? //TODO NOT GOING TO DO THIS
    case (_, TInterface(tvar, t2p)) => ??? //TODO NOT GOING TO DO THIS
    /***** Otherwise, false. */
    case _ => false
  }

  /*** Type Inference ***/

  type TEnv = Map[String, (Mutability,Typ)]
  val emp: TEnv = Map()
  def get(env: TEnv, x: String): (Mutability,Typ) = env(x)
  def extend(env: TEnv, x: String, mt: (Mutability,Typ)): TEnv = env + (x -> mt)

  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  // A helper function to translate parameter passing mode to the mutability of
  // the variable.
  def mut(m: PMode): Mutability = m match {
    case PName => MConst
    case PVar | PRef => MVar
  }

  def typeInfer(env: TEnv, e: Expr): Typ = {
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) =>
        val (_, t) = env(x)
        t
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      /***** Cases directly from Lab 4. We will minimize the test of these cases in Lab 5. */
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typ(e1),typ(e2)) match {
        case (TString,a) => if (a==TString) TString else err(a,e2)
        case (TNumber,a) => if (a==TNumber) TNumber else err(a,e2)
        case _ => err(typ(e1),e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typ(e1),typ(e2)) match {
        case (TNumber,a) => if (a==TNumber) TNumber else err(a,e2)
        case _ => err(typ(e1),e1)
      }
      case Binary(Eq|Ne, e1, e2) => (typ(e1),typ(e2)) match {
        case (a,b) => a match {
          case TFunction(_,_) => err(a,e1)
          case z => if (b == z) TBool else err(b,e2)
        }
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typ(e1),typ(e2)) match {
        case (TString,a) => if (a==TString) TBool else err(a,e2)
        case (TNumber,a) => if (a==TNumber) TBool else err(a,e2)
        case _ => err(typ(e1), e1)
      }
      case Binary(And|Or, e1, e2) => (typ(e1),typ(e2)) match {
        case (TBool,a) => if (a==TBool) TBool else err(a,e2)
        case _ => err(typ(e1),e1)
      }
      case Binary(Seq, e1, e2) => typ(e1);typ(e2)
      case If(e1, e2, e3) => (typ(e1),typ(e2),typ(e3)) match {
        case (TBool,a,b) => if (a == b) a else err(b,e3)
        case (x,_,_) => err(x,e1)
      }
      case Obj(fields) => {
        TObj(fields.map({
          case (e,t) => (e,typ(t))
        }))
      }
      case GetField(e1, f) => typ(e1) match {
        case TObj(obj) => obj.get(f) match {
          case None => err(typ(e1), e1)
          case Some(thing) => thing
        }
        case _ => err(typ(e1),e1)
      }
      /***** Cases from Lab 4 that need a small amount of adapting. */
      case Decl(mut, x, e1, e2) => {
        val env1 = extend(env, x, (mut, typ(e1)))
        typeInfer(env1, e2)
      }
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            env+(f->(MConst,tprime))
          case (None, _) => env
          case (_,_) => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params match {
          case Left(p) => p.foldLeft(env1)((acc, b) => acc + (b._1 -> (MConst,b._2)))
          case Right((mode,x1,t1)) => extend(env1,x1,(mut(mode),t1))
          case _ => err(typ(e1),e1)
        }
        // Match on whether the return type is specified.
        val t = typeInfer(env2,e1)
        tann match {
          case None => TFunction(params,t)
          case Some(tret) => {
            if (tret != t)
              TFunction(params,err(tret,e1))
            else
              TFunction(params,t)
          }
        }
      }
      case Call(e1, args) => typ(e1) match {
        case TFunction(Left(params), tret) if params.length == args.length => {
          (params, args).zipped.foreach {
            (p, arg) => (p, arg) match {
              case ((str, t), argtype) => if (t != typeInfer(env, argtype)) err(typeInfer(env, argtype), argtype)
              case _ => tret
            }
          };
          tret
        }
        case tgot @ TFunction(Right((mode,_,tparam)), tret) => mode match {
          case PRef => args match {
            case h::_ => if (typeInfer(env,h) == tparam && isLExpr(h)) tret else err(typeInfer(env,h),h)
            case _ => err(tgot,e1)
          }
          case _ => args match {
            case h::_ => if(typeInfer(env,h) == tparam) tret else err(typeInfer(env,h),h)
            case _ => err(tgot,e1)
          }
        }
        case _ => err(typ(e1), e1)
      }

      /***** New cases for Lab 5. ***/
      case Assign(Var(x), e1) => env.get(x) match {
        case Some((MVar, t)) => if (t == typ(e1)) t else err(typ(e1), e1)
        case _ => err(typ(e1), e1)
      }
      case Assign(GetField(e1, f), e2) => typ(e1) match {
        case TObj(fields) => if (fields(f) == typ(e2)) typ(e2) else err(typ(e2), e2)
        case _ => err(typ(e1), e1)
      }
      case Assign(_, _) => err(TUndefined, e)
      case Null => TNull
      case Unary(Cast(t), e1) => typ(e1) match {
        case tgot if castOk(typ(e1),t) => t  //maybe tgot(e1)
        case tgot => err(tgot, e1)
      }

      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  /*** Small-Step Interpreter ***/

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3 and Lab 4.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), "v1 in inequalityVal is not a value")
    require(isValue(v2), "v2 in inqualityVal is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2) : @unchecked) match {
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

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    /* We removed the requirement that esub is a value to support call-by-name. */
    //require(isValue(esub), "Expr to substitute is not a value")
    /* We suggest that you add support for call-by-name last. */
    def subst(e: Expr): Expr = substitute(e, esub, x)
    val ep: Expr = avoidCapture(freeVars(esub),e)
    ep match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
      /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop,subst(e1))
      case Binary(bop,e1,e2) => Binary(bop,subst(e1),subst(e2))
      case If(e1,e2,e3) => If(subst(e1),subst(e2),subst(e3))
      case Var(y) => if(x == y) esub else Var(y)
      /***** Cases need a small adaption from Lab 3 */
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
      /***** Cases needing adapting from Lab 4 */
      case Function(p, paramse, retty, e1) => paramse match {
        case Left(params) =>
          if (params.foldLeft(false)((b, param) => (param._1 == x) || b) || Some(x) == p) e
          else Function(p, paramse, retty, subst(e1))

        case Right((_, x1, t)) =>
          if (x == x1 || Some(x) == p) e
          else Function(p, paramse, retty, subst(e1))
      }
      /***** Cases directly from Lab 4 */
      case Call(e1, args) => Call(subst(e1),args map subst)
      case Obj(fields) => Obj(fields map (field => (field._1,subst(field._2))))
      case GetField(e1, f) => GetField(subst(e1),f)
      /***** New case for Lab 5 */
      case Assign(e1, e2) => Assign(subst(e1),subst(e2))
      /***** Extra credit case for Lab 5 */
      case InterfaceDecl(tvar, t, e1) => ??? // TODO NOT GOING TO DO THIS
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))

    /*** Helpers for Call ***/

    def stepIfNotValue(e: Expr): Option[DoWith[Mem,Expr]] = if (isValue(e)) None else Some(step(e))

    /* Check whether or not the argument expression is ready to be applied. */
    def argApplyable(mode: PMode, arg: Expr): Boolean = mode match {
      case PVar => isValue(arg)
      case PName => true
      case PRef => isLValue(arg)
    }

    /*** Body ***/
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
      /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Unary(Neg, N(n)) => doreturn(N(-n))
      case Unary(Not, B(b)) => doreturn(B(!b))
      case Binary(Plus, N(n),N(n2)) => doreturn(N(n+n2))
      case Binary(Plus,S(s),S(s2)) => doreturn(S(s+s2))
      case Binary(Minus,N(n),N(n2)) => doreturn(N(n-n2))
      case Binary(Times, N(n),N(n2)) => doreturn(N(n*n2))
      case Binary(Div,N(n),N(n2)) => doreturn(N(n/n2))
      case Binary(And,B(b),e2) => if (b==true) doreturn(e2) else doreturn(B(false))
      case Binary(Or,B(b),e2) => if (b==true) doreturn(B(true)) else doreturn(e2)
      case Binary(Eq,v1,v2) if isValue(v1) && isValue(v2) => doreturn(B(v1 == v2))
      case Binary(Ne,v1,v2) if isValue(v1) && isValue(v2) => doreturn(B(v1 != v2))
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => doreturn(B(inequalityVal(bop, v1, v2)))
      case Binary(Seq, v1, e2) if isValue(v1) => doreturn(e2)
      case If(B(true),e1,e2) => doreturn(e1)
      case If(B(false),e1,e2) => doreturn(e2)
      /***** Cases needing adapting from Lab 4. Make sure to replace the case _ => ???. */
      case Obj(fields) if fields forall { case (_, vi) => isValue(vi)} =>
        memalloc(e) // get fresh memory address w/ memory cell contents initialized to the contents of e.
      case GetField(a @ A(_), f) => {
        doget map {m => m.get(a) match {
          case Some(thing) => thing match {
            case Obj(fields) => fields(f)
            case _ => throw StuckError(e)
          }
          case None => throw StuckError(e)
        }}
      }
      case Call(v1, args) if isValue(v1) =>
        def substfun(e1: Expr, p: Option[String]): Expr = p match {
          case None => e1
          case Some(x) => substitute(e1, v1, x)
        }
        (v1, args) match {
          /*** Fill-in the DoCall cases, the SearchCall2, the SearchCallVar, the SearchCallRef  ***/
          case (Function(p,Left(params),_,e1),args) => {
            if ((args forall isValue) && params.length == args.length) {
              val e1p = (params, args).zipped.foldRight(e1) {
                (a, acc) => substitute(acc, a._2, a._1._1)
              }
              p match {
                case None => doreturn(e1p)
                case Some(thing) => doreturn(substitute(e1p,v1,thing))
              }
            }
            else mapFirstWith[Mem,Expr](ex => if (isValue(ex)) None else Some(step(ex)))(args) map {argsp => Call(v1,argsp)}
          }
          case (Function(p,Right((PName,x1,_)),_,e1),e2::Nil) => doreturn(substfun(substitute(e1,e2,x1),p))
          case (Function(p,Right((PRef,x1,_)),_,e1),lv::Nil) => {
            if (isLValue(lv)) doreturn(substfun(substitute(e1, lv, x1), p)) else step(lv) map { lv2 => Call(v1, lv2 :: Nil) }
          }
          case (Function(p,Right((PVar,x1,_)),_,e1),v2::Nil) => {
            if (isValue(v2)) memalloc(v2) map {a => substfun(substitute(e1,Unary(Deref,a),x1),p)}
            else step(v2) map {v2p => Call(v1,v2p::Nil)}
          }
          case _ => throw StuckError(e)
        }

      case Decl(MConst, x, v1, e2) if isValue(v1) =>
        doreturn(substitute(e2,v1,x))
      case Decl(MVar, x, v1, e2) if isValue(v1) => {
        memalloc(v1) map {a => substitute(e2,Unary(Deref,a),x)}
      }

      /***** New cases for Lab 5. */
      case Unary(Deref, a @ A(_)) => {
        doget map {x1 => x1.get(a) match {
          case Some(name) => name
          case None => throw StuckError(e)
        }
        }
      }

      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        domodify[Mem] {m => m + (a->v)} map {_ => v}
      case Assign(GetField(a @ A(_), f), v) if isValue(v) => {
        //if (v == Null) throw NullDereferenceError(e)
        domodify[Mem] {
          m => val newField = m.get(a) match {
            case Some(Obj(fields)) => Obj(fields + (f -> v))
            case _ => throw StuckError(e)
          }
            m + (a -> newField)} map {_ => v}
      }
      case Unary(Cast(t),e) =>
        if (isValue(e) || e == Null) doreturn(e)
        else (t,e) match {
          case (TObj(fields), a @ A(_)) => if (castOk(t,typeInfer(Map(), e))) doreturn(a) else throw DynamicTypeError(e)
          // case (TInterface(tvar,t), a @ A(_)) => if (castOk(t,typeInfer(Map(), e))) doreturn(a) else throw DynamicTypeError(e)
          case _ => step(e) map {ep => Unary(Cast(t),ep)}
        }
      /* Base Cases: Error Rules */
      /***** Replace the following case with a case to throw NullDeferenceError.  */
      //case _ => throw NullDeferenceError(e)

      /* Inductive Cases: Search Rules */
      /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Print(e1) => step(e1) map { e1p => Print(e1p) }
      case Unary(uop, e1) => step(e1) map {e1p => Unary(uop,e1p)}
      case Binary(bop,v1,e2) if isValue(v1)=> step(e2) map {e2p => Binary(bop,v1,e2p)}
      case Binary(bop,e1,e2) => step(e1) map {e1p => Binary(bop,e1p,e2)}
      case If(e1,e2,e3) => step(e1) map {e1p => If(e1p,e2,e3)}
      case Call(v1 @ Function(_,_,_,_), args) => mapFirstWith(stepIfNotValue)(args) map {argsp => Call(v1, argsp) }
      case Call(e1, args) => step(e1) map {e1p => Call(e1p, args)}
      case Decl(mut, x, e1, e2) => step(e1) map {e1p => Decl(mut,x,e1p,e2)}
      /***** Cases needing adapting from Lab 4 */
      case GetField(e1, f) => {
        if (e1==Null) throw NullDereferenceError(e) else step(e1) map {e1p => GetField(e1p,f)}
      }
      case Obj(fields) => { fields find { case (_, ei) => !isValue(ei) } match {
        case Some((x1,x2)) => step(x2) map {x2p => Obj(fields + (x1->x2p))}
        case None => throw StuckError(e)
      }
      }
      /***** New cases for Lab 5.  */
      case Assign(lv1, e2) if isLValue(lv1) =>
        step(e2) map {e2p => Assign(lv1,e2p)}
      case Assign(e1, e2) =>
        if (isValue(e1)) throw StuckError(e) else step(e1) map {e1p => Assign(e1p,e2)}

      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
    }
  }

  /*** Extra Credit: Lowering: Remove Interface Declarations ***/

  def removeInterfaceDecl(e: Expr): Expr =
  /* Do nothing by default. Change to attempt extra credit. */
    e

  /*** External Interfaces ***/

  //this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.

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

  case class TerminationError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }

  def iterateStep(e: Expr): Expr = {
    require(closed(e), "input Expr to iterateStep is not closed: free variables: %s".format(freeVars(e)) )
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e)
      else if (isValue(e)) doreturn( e )
      else {
        for {
          m <- doget[Mem]
          _ = if (debug) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
          ep <- step(e)
          epp <- loop(ep, n + 1)
        } yield
          epp
      }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val (m,v) = loop(e, 0)(memempty)
    if (debug) {
      println("Result:%n  %s%n  %s".format(m,v))
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(removeInterfaceDecl(jsy.lab5.Parser.parse(s)))

  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }

    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab5.Parser.parseFile(file)
      }} getOrElse {
        return
      }

    val exprlowered =
      handle(None: Option[Expr]) {Some{
        removeInterfaceDecl(expr)
      }} getOrElse {
        return
      }

    val welltyped = handle(false) {
      println("# Type checking ...")
      val t = inferType(exprlowered)
      println("## " + pretty(t))
      true
    }
    if (!welltyped) return

    handle() {
      println("# Stepping ...")
      def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
        if (Some(n) == maxSteps) throw TerminationError(e)
        else if (isValue(e)) doreturn( e )
        else {
          for {
            m <- doget[Mem]
            _ = println("## %4d:%n##  %s%n##  %s".format(n, m, e))
            ep <- step(e)
            epp <- loop(ep, n + 1)
          } yield
            epp
        }
      val (m,v) = loop(exprlowered, 0)(memempty)
      println("## %s%n%s".format(m,pretty(v)))
    }
  }

}