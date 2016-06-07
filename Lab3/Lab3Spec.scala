import org.scalatest._
import jsy.tester.JavascriptyTester
import jsy.lab3.ast._
import jsy.lab3.Parser.parse


import jsy.student.Lab3
import Lab3._

class ConversionSpec extends FlatSpec {
  // tests for type conversions.
  "toNumber" should "return the appropriate numerical conversion" in {
    val l = N(1)
    val n = N(1.2)
    val m = N(-1.2)
    val t = B(true)
    val f = B(false)
    val s = S("hello")
    val s2 = S("2.1")
    assert(toNumber(l) === 1)
    assert(toNumber(n) === 1.2)
    assert(toNumber(m) === -1.2)
    assert(toNumber(Undefined).isNaN)
    assert(toNumber(t) === 1.0)
    assert(toNumber(f) === 0.0)
    assert(toNumber(s).isNaN)
    assert(toNumber(s2) === 2.1)
    //add function test here
  }
  "toBoolean" should "return the Boolean equivalent of the input" in {
    val n0 = N(0)
    val n1 = N(1)
    val n2 = N(1.5)
    val s1 = S("")
    val s2 = S("hello")
    val t = B(true)
    val f = B(false)
    assert(toBoolean(n0) === false)
    assert(toBoolean(n1) === true)
    assert(toBoolean(n2) === true)
    assert(toBoolean(s1) === false)
    assert(toBoolean(s2) === true)
    assert(toBoolean(t) === true)
    assert(toBoolean(f) === false)
    assert(toBoolean(Undefined) === false)
    //add function test here.
  }
  "toString" should "return the corresponding string characterization of the input" in {
    val t = B(true)
    val f = B(false)
    val n0 = N(1)
    val n1 = N(2.0)
    val n2 = N(2.5)
    val n3 = N(-2.5)
    val n4 = N(-1)
    val s = S("hello")
    assert(toStr(t) === "true")
    assert(toStr(f) === "false")
    assert(toStr(n0) === "1")
    assert(toStr(n1) === "2")
    assert(toStr(n2) === "2.5")
    assert(toStr(n3) === "-2.5")
    assert(toStr(n4) === "-1")
    assert(toStr(s) === "hello")
    // add function test here.
  }
}

class ArithmeticSpec extends FlatSpec{
  
  "Plus" should "return decimal numerical addition including non intuitive results" in {
    val a = N(1)
    val b = N(2)
    val t = B(true)
    val f = B(false)
    val s = S("hello")
    assert (evaluate(Binary(Plus, a, b))=== N(3))
    assert (evaluate(Binary(Plus, a, t)) === N(2))
    assert (evaluate(Binary(Plus, a, f)) === N(1))
    assert (evaluate(Binary(Plus, a, s)) === S("1hello"))
    assert (evaluate(Binary(Plus, s, a)) === S("hello1"))
  }
  "Minus" should "subtract two numbers and return a number including non intuitive results" in {
    val a = N(1)
    val b = N(3)
    val t = B(true)
    val f = B(false)
    assert (evaluate(Binary(Minus, b, a)) === N(2))
    assert (evaluate(Binary(Minus, a, b)) === N(-2))
    assert (evaluate(Binary(Minus, a, t)) === N(0))
    assert (evaluate(Binary(Minus, a, f)) === N(1))
  }
  "Times" should "multiply two numbers and return a number including non intuitive results." in {
    val e1 = N(2)
    val e2 = N(3)
    val e3 = N(2.5)
    val e4 = N(-2.5)
    val t = B(true)
    val f = B(false)
    assert(evaluate(Binary(Times, e1, e2)) === N(6))
    assert(evaluate(Binary(Times, e1, e3)) === N(5.0))
    assert(evaluate(Binary(Times, e1, e4)) === N(-5.0))
    assert(evaluate(Binary(Times, e1, t)) === N(2))
    assert(evaluate(Binary(Times, e1, f)) === N(0))
  }
  "Div" should "Divide two numbers and return a number including non intuitive results" in {
    val e1 = N(6)
    val e2 = N(2)
    val e3 = N(-2)
    val e4 = N(1.5)
    val t = B(true)
    assert(evaluate(Binary(Div, e1, e2)) === N(3))
    assert(evaluate(Binary(Div, e1, e3)) === N(-3))
    assert(evaluate(Binary(Div, e1, t)) === N(6))
    assert(evaluate(Binary(Div, e1, e4)) === N(4))
  }
}

class ComparisonSpec extends FlatSpec {
  "Eq" should "return true if two numerical values are the same" in {
    val e1 = N(5)
    val e2 = N(5)
    val e3 = evaluate(Binary(Eq, e1, e2))
    val e4 = Undefined
    val e5 = Undefined
    val e6 = evaluate(Binary(Eq, e4, e5))
    val s1 = S("black")
    val s2 = evaluate(Binary(Eq, s1, s1))
    assert(e3 === B(true))
    assert(e6 === B(true))
    assert(s2 == B(true))
  }
  "Eq" should "return false if two numerical values are not the same" in {
    val e1 = N(5)
    val e2 = N(7)
    val e3 = evaluate(Binary(Eq, e1, e2))
    val s1 = S("white")
    val s2 = S("black")
    val s3 = evaluate(Binary(Eq, s1, s2))
    assert(e3 === B(false))
    assert(s3 === B(false))
    assert(evaluate(Binary(Eq, Undefined, Undefined)) === B(true))
  }
  "Eq" should "return false if the types are dissimilar" in {
    val e1 = N(1)
    val e2 = B(true)
    val e3 = evaluate(Binary(Eq, e1, e2))
    assert(e3 === B(false))
  }
  "Ne" should "return true if two numerical values are different" in {
    val e1 = N(5)
    val e2 = N(7)
    val e3 = evaluate(Binary(Ne, e1, e2))
    assert(e3 === B(true))
  }
  "Ne" should "return false if two numerical values are the same" in {
    val e1 = N(5)
    val e2 = N(5)
    val e3 = evaluate(Binary(Ne, e1, e2))
    val e4 = evaluate(Binary(Ne, Undefined, Undefined))
    assert(e3 === B(false))
    assert(e4 === B(false))
    assert(evaluate(Binary(Ne, Undefined, Undefined)) === B(false))
  }
  "Lt" should "return true if the first expression is less than the second" in {
    val e1 = N(5)
    val e2 = N(7)
    val e3 = evaluate(Binary(Lt, e1, e2))
    val s1 = S("happy")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Lt, s1, s2))
    assert(e3 === B(true))
    assert(s3 === B(true))

  }
  "Lt" should "return false if the first expression is not strictly less than the second" in {
    val e1 = N(7)
    val e2 = N(5)
    val e3 = evaluate(Binary(Lt, e1, e2))
    val s1 = S("happy")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Lt, s2, s1))
    assert(e3 === B(false))
    assert(s3 === B(false))
  }
  "Lt" should "return false if two number values are the same" in {
    val e1 = N(5)
    val e2 = N(5)
    val e3 = evaluate(Binary(Lt, e1, e2))
    val s1 = S("sad")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Lt, s1, s2))
    assert(e3 === B(false))
    assert(s3 === B(false))
  }
  "Le" should "return true if the first expression is less than the second" in {
    val e1 = N(5)
    val e2 = N(7)
    val e3 = evaluate(Binary(Le, e1, e2))
    val s1 = S("happy")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Le, s1, s2))
    assert(e3 === B(true))
    assert(s3 === B(true))
  }
  "Le" should "return false if the first expression is greater than the second" in {
    val e1 = N(7)
    val e2 = N(5)
    val e3 = evaluate(Binary(Le, e1, e2))
    val s1 = S("happy")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Le, s2, s1 ))
    assert(e3 === B(false))
    assert(s3 === B(false))
  }
  "Le" should "return true if two number values are the same" in {
    val e1 = N(5)
    val e2 = N(5)
    val e3 = evaluate(Binary(Le, e1, e2))
    val s1 = S("sad")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Le, s2, s1 ))
    assert(e3 === B(true))
    assert(s3 === B(true))
  }
  "Gt" should "return true if the first expression is greater than the second" in {
    val e1 = N(8)
    val e2 = N(7)
    val e3 = evaluate(Binary(Gt, e1, e2))
    val s1 = S("happy")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Gt, s2, s1 ))
    assert(e3 === B(true))
    assert(s3 === B(true))
  }
  "Gt" should "return false if the first expression is not strictly greater than the second" in {
    val e1 = N(4)
    val e2 = N(5)
    val e3 = evaluate(Binary(Gt, e1, e2))
    val s1 = S("happy")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Gt, s1, s2 ))
    assert(e3 === B(false))
    assert(s3 === B(false))
  }
  "Gt" should "return false if two number values are the same" in {
    val e1 = N(5)
    val e2 = N(5)
    val e3 = evaluate(Binary(Gt, e1, e2))
    val s1 = S("sad")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Gt, s2, s1 ))
    assert(e3 === B(false))
    assert(s3 === B(false))
  }
  "Ge" should "return true if the first expression is greater than the second" in {
    val e1 = N(8)
    val e2 = N(7)
    val e3 = evaluate(Binary(Ge, e1, e2))
    val s1 = S("happy")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Gt, s2, s1 ))
    assert(e3 === B(true))
    assert(s3 === B(true))
  }
  "Ge" should "return false if the first expression is less than the second" in {
    val e1 = N(4)
    val e2 = N(5)
    val e3 = evaluate(Binary(Ge, e1, e2))
    val s1 = S("happy")
    val s2 = S("sad")
    val s3 = evaluate(Binary(Gt, s1, s2 ))
    assert(e3 === B(false))
    assert(s3 === B(false))
  }
  "Ge" should "return true if two number values are the same" in {
    val e1 = N(5)
    val e2 = N(5)
    val e3 = evaluate(Binary(Ge, e1, e2))
    val s1 = S("sad")
    val s3 = evaluate(Binary(Ge, s1, s1 ))
    assert(e3 === B(true))
    assert(s3 === B(true))
  }
  "Comparisons" should "produce non-intuitive results given the expressions given" in {
    val e1 = N(5)
    val e2 = Undefined
    assert(evaluate(Binary(Eq,e1,e2)) === B(false))
  }
}

class ConstSpec extends FlatSpec {
  "ConstDecl" should "extend the environment with the first expression results bound to the identifier, and then eval the second expression" in {
    val e1 = N(3)
    val e2 = Binary(Plus, Var("x"), N(1))
    val e3 = evaluate(ConstDecl("x", e1, e2))
    assert(e3 === N(4))
  }
}

class IfSpec extends FlatSpec {
  "If" should "eval the first expression if the conditional is true" in {
    val e1 = Binary(Plus, N(3), N(2))
    val e2 = Binary(Plus, N(1), N(1))
    val e3 = evaluate(If(B(true), e1, e2))
    assert(e3 === N(5))
  }

  "If" should "eval the second expression if the conditional is false" in {
    val e1 = Binary(Plus, N(3), N(2))
    val e2 = Binary(Plus, N(1), N(1))
    val e3 = evaluate(If(B(false), e1, e2))
    assert(e3 === N(2))
  }
}

class SeqSpec extends FlatSpec {
  "Seq" should "execute the first expression, followed by the second, and should eval to the second expression" in {
    val e1 = Binary(Plus, N(3), N(2))
    val e2 = Binary(Plus, N(1), N(1))
    val e3 = evaluate(Binary(Seq, e1, e2))
    assert(e3 === N(2))
  }
}

class UnarySpec extends FlatSpec {
  "Neg" should "return the negation of a number value" in {
    val e1 = N(5)
    val e2 = evaluate(Unary(Neg, e1))
    assert(e2 === N(-5))
  }

  "Not" should "return the compliment of a boolean value" in {
    val e1 = B(true)
    val e2 = B(false)
    val e3 = evaluate(Unary(Not, e1))
    val e4 = evaluate(Unary(Not, e2))
    assert(e3 === B(false))
    assert(e4 === B(true))
  }
}

class AndOrSpec extends FlatSpec {
  "And" should "evaluate the second expression if the first expression is true" in {
    assert(evaluate(Binary(And, B(true), Binary(Times, N(6.0), N(7.0)))) === N(42))
    //assert(evaluate(Binary(And, Print(S("e")), Print(S("f")))) === Undefined)
    //assert(evaluate(Binary(And, Undefined, Print(S("f")))) === Undefined)
    //assert(evaluate(Binary(Seq,Binary(And,Print(S("e")),Print(S("f"))),Binary(Or,Print(S("g")),Print(S("h"))))) === Undefined)
    assert(evaluate(Binary(Seq,Binary(And,B(false),Print(S("a"))),Binary(Seq,Binary(And,B(true),Print(S("b"))),Binary(Seq,Binary(Or,B(false),Print(S("c"))),Binary(Seq,Binary(Or,B(true),Print(S("d"))),Binary(Seq,Binary(And,Print(S("e")),Print(S("f"))),Binary(Or,Print(S("g")),Print(S("h"))))))))) === Undefined)
  }

  "And" should "not evaluate the second expression and return the value of the first expression if false" in {
    assert(evaluate(Binary(And, Binary(And, N(1.0), N(0.0)), Binary(Times, N(6.0), N(7.0)))) === N(0))
  }
  "Or" should "return true if the first expression is true" in {
    assert(evaluate(Binary(Or, B(true), Binary(Times, N(6.0), N(7.0)))) === B(true))
    //assert(evaluate(Binary(Or, Print(S("f")), Print(S("e")))) === Undefined)
  }
  "Or" should "evaluate the second expression if the first expression is false" in {
    assert(evaluate(Binary(Or, B(false), Binary(Times, N(6.0), N(7.0)))) === N(42.0))
  }
}

class FunctionCallSpec extends FlatSpec {
  "Functions" should "be considered values" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Var(x))
    val e2 = Function(Some(f), x, Var(x))
    assert(evaluate(e1) == e1)
    assert(evaluate(e2) == e2)
  }

  "Call" should "evaluate a function using big-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = evaluate(Call(e1, e2))
    assert(e3 === N(3))
  }

  "Call" should "handle recursive functions using big-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Function(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = evaluate(Call(e1, e2))
    assert(e3 === N(6))
  }

  "Call" should "evaluate a function using small-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === N(3))
  }

  "Call" should "handle recursive functions using small-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Function(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === N(6))
  }

}

class SubstituteSpec extends FlatSpec {
  "substitute" should "perform syntatic substitution respecting shadowing" in {
    val xplus1 = parse("x + 1")
    val twoplus1 = parse("2 + 1")
    assert(substitute(xplus1, N(2), "x") === twoplus1)
    val constx3 = parse("const x = 3; x")
    val shadowx = Binary(Plus, constx3, Var("x"))
    assert(substitute(shadowx, N(2), "x") === Binary(Plus, constx3, N(2)))
  }
  it should "perform simple substitution" in {
    assertResult(N(42.0)) {
      substitute(Var("x"), N(42), "x")
    }
  }
}

class RulesSpec extends FlatSpec {
  /* Tests based on rules */

  val xval = N(2)
  val envx = extend(emp, "x", xval)
  val varx = Var("x")

  val e1 = parse("2 - 1 - 1")
  val e1p = parse("1 - 1")
  val e2 = parse("3 - 1 - 1")
  val e2p = parse("2 - 1")
  val v1 = N(0)
  val v2 = N(1)

  val vidfunction = parse("function (x) { return x }")

  "S + S" should "concatenate strings" in {
    assertResult(S("hellohello")) {
      step(Binary(Plus,S("hello"),S("hello")))
    }
  }
  "S == S" should "compare two strings and return true if equal" in {
    assertResult(B(true)) {
      step(Binary(Eq,S("hellohello"), S("hellohello")))
    }
  }

  "EvalVar" should "perform EvalVar" in {
    assertResult(xval) {
      eval(envx, varx)
    }
  }
  "EvalNeg" should "perform EvalNeg" in {
    val np = -toNumber(v1)
    assertResult(N(np)) {
      eval(envx, Unary(Neg, e1))
    }
  }
  "EvalTypeErrorEquality1" should "perform EvalTypeErrorEquality1" in {
    intercept[DynamicTypeError] {
      eval(envx, Binary(Eq, vidfunction, e2))
    }
  }
  "DoNeg" should "perform DoNeg" in {
    val np = -toNumber(v1)
    assertResult(N(np)) {
      step(Unary(Neg, v1))
    }
  }
  "DoNot" should "perform DoNot" in {
    val np = !toBoolean(v1)
    assertResult(B(np)) {
      step(Unary(Not, v1))
    }
  }
  "DoSeq" should "return the second operand" in {
    assertResult(Binary(Times,N(6.0),N(7.0))){
      step(Binary(Seq,N(1.0),Binary(Times,N(6.0),N(7.0))))
    }
  }
  "DoPlusNumber" should "add values that are not strings" in {
    assertResult(N(2.0)) {
      step(Binary(Plus, N(1.0), B(true)))
    }
  }
  "DoPlusString" should "concatenate values when one is a string" in {
    assertResult(S("hi2")) {
      step(Binary(Plus,S("hi"),N(2.0)))
    }
    assertResult(S("2hi")) {
      step(Binary(Plus,N(2.0),S("hi")))
    }
  }
  "DoArith" should "perform value arithmetic" in {
    assertResult(N(3.0)) {
      step(Binary(Times, N(1.0), N(3.0)))
    }
    assertResult(N(3.0)) {
      step(Binary(Div, N(3.0), N(1.0)))
    }
    assertResult(N(2.0)) {
      step(Binary(Minus, N(3.0), N(1.0)))
    }
  }
  "DoInequalityNumber1&2" should "perform inequality operations on numbers" in {
    assertResult(B(false)) {
      step(Binary(Lt,N(17.0),N(13.0)))
    }
    assertResult(B(false)) {
      step(Binary(Le,N(17.0),N(13.0)))
    }
    assertResult(B(true)) {
      step(Binary(Gt,N(17.0),N(13.0)))
    }
    assertResult(B(true)) {
      step(Binary(Ge,N(17.0),N(13.0)))
    }
  }
  "DoInequalityString" should "perform inequality operations on strings" in {
    assertResult(B(true)) {
      step(Binary(Lt,S("happy"),S("sad")))
    }
    assertResult(B(true)) {
      step(Binary(Le,S("happy"),S("sad")))
    }
    assertResult(B(false)) {
      step(Binary(Gt,S("happy"),S("sad")))
    }
    assertResult(B(false)) {
      step(Binary(Ge,S("happy"),S("sad")))
    }
  }
  "DoEquality" should "perform value comparisons provided no functions" in {
    assertResult(B(false)) {
      step(Binary(Eq,N(3.0),N(4.0)))
    }
    assertResult(B(true)) {
      step(Binary(Ne, N(3.0), N(4.0)))
    }
  }
  "DoAndTrue" should "evaluate e2 is v1 is true" in {
    assertResult(Binary(Plus, N(1.0), N(2.0))) {
      step(Binary(And,B(true),Binary(Plus,N(1.0),N(2.0))))
    }
  }
  "DoAndFalse" should "return v1 if v1 == false" in {
    assertResult(B(false)) {
      step(Binary(And,B(false), Binary(Plus,N(1.0),N(2.0))))
    }
  }
  "DoOrTrue" should "return v1 if v1 == true" in {
    assertResult(B(true)) {
      step(Binary(Or, B(true), Binary(Plus, N(1.0), N(2.0))))
    }
  }
  "DoOrFalse" should "evaluate e2 if v1 == false" in {
    assertResult( Binary(Plus, N(1.0), N(2.0))) {
      step(Binary(Or, B(false), Binary(Plus, N(1.0), N(2.0))))
    }
  }
  "DoPrint" should "return undefined if v has been printed" in {
    assertResult(Undefined) {
      step(Print(N(1.0)))
    }
  }
  "DoIfTrue" should "evaluate e2 if v1 if true" in {
    assertResult(Binary(Plus,N(1.0), N(2.0))){
      step(If(B(true), Binary(Plus,N(1.0), N(2.0)), Binary(Plus,N(2.0), N(3.0))))
    }
  }
  "DoIfFalse" should "evaluate e3 if v1 is false" in {
    assertResult(Binary(Plus, N(2.0), N(3.0))) {
      step(If(B(false), Binary(Plus, N(1.0), N(2.0)), Binary(Plus, N(2.0), N(3.0))))
    }
  }
  "DoConst" should "set variable in e2 to v1" in {
    assertResult(Binary(Plus,N(1.0),N(2.0))) {
      step(ConstDecl("x", N(1.0), Binary(Plus, Var("x"), N(2.0))))
    }
  }

  "SearchUnary" should "perform SearchUnary" in {
    assertResult(Unary(Neg, e1p)) {
      step(Unary(Neg, e1))
    }
    assertResult(Unary(Neg, N(3.0))) {
      Unary(Neg, step(Binary(Plus, N(1.0), N(2.0))))
    }
    assertResult(Unary(Not, N(3.0))){
      step(Unary(Not,Binary(Plus,N(1.0),N(2.0))))
    }
  }
  "SearchBinary1" should "step its first argument (if expression)" in {
    assertResult(Binary(Plus,N(-42.0),N(40.0))){
      Binary(Plus, step(Unary(Neg, N(42.0))), N(40.0))
    }
    assertResult(Binary(Plus, N(0.0), N(0.1))) {
      Binary(Plus,step(Binary(And,N(1.0),N(0.0))),N(0.1))
    }
  }
  "SearchBinaryArith2" should "step its second argument (if expression)" in {
    assertResult(Binary(Plus,N(1.0), N(30.0))) {
      Binary(Plus, N(1.0), step(Binary(Times, N(6.0), N(5.0))))
    }
  }
  "SearchAnd" should "step its first argument (if expression)" in {
    assertResult(Binary(And,Undefined,Print(S("f")))) {
      step(Binary(And,Print(S("e")),Print(S("f"))))
    }
  }
  "SearchEquality" should "step its second argument (if expression)" in {
    assertResult(Binary(Eq, N(1.0), N(3.0))) {
      Binary(Eq, N(1.0), step(Binary(Plus,N(1.0),N(2.0))))
    }
    assertResult(Binary(Ne, N(1.0), N(3.0))) {
      Binary(Ne, N(1.0), step(Binary(Plus,N(1.0),N(2.0))))
    }
  }
  "SearchPrint" should "step in evaluation of e1" in {
    assertResult(Print(N(3.0))) {
      Print(step(Binary(Plus, N(1.0), N(2.0))))
    }
  }
  "SearchConst" should "step in evaluation of e1" in {
    assertResult(ConstDecl("x", N(8),Binary(Plus,Var("x"),N(2.0)))){
      ConstDecl("x",step(Binary(Plus,N(1.0),N(7.0))),Binary(Plus,Var("x"),N(2.0)))
    }
  }
}

// The next bit of code runs a test for each .jsy file in src/test/resources/lab3.
// The test expects a corresponding .ans file with the expected result.
class Lab3JsyTests extends JavascriptyTester(None, "lab3", Lab3)

class Lab3Suite extends Suites(
  new FunctionCallSpec,
  new SubstituteSpec,
  new RulesSpec,
  new Lab3JsyTests
)
