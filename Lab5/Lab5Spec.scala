import jsy.util.DoWith
import org.scalatest._
import jsy.tester.JavascriptyTester
import jsy.lab5._
import jsy.lab5.ast._
import DoWith._
import jsy.lab5.Parser.parse

import jsy.student.Lab5
import Lab5._

class Lab5ExercisesSpec extends FlatSpec {

  "rename" should "rename from left-to-right using fresh" in {
    val e1 = parse("const a = 1; a")
    val e1p = parse("const x1 = 1; x1")
    val e2 = parse("const a = 2; a")
    val e2p = parse("const x2 = 2; x2")
    val e = Decl(MConst, "a", e1, e2)
    val ep = Decl(MConst, "x0", e1p, e2p)
    assertResult(ep) { rename(e) }
  }
  
  "mapFirstDoWith" should "map the first element where f returns Some" in {
     val l1 = List(1, 2, -3, 4, -5)
     val gold1 = List(1, 2, 3, 4, -5)
     def dowith[W]: DoWith[W,List[Int]] = mapFirstWith[W,Int] { (i: Int) => if (i < 0) Some(doreturn(-i)) else None } (l1)
     assertResult((true,gold1)) { dowith(true) }
     assertResult((42,gold1)) { dowith(42) }
  }

}
class RenameSpec extends FlatSpec {
  "Rename" should "do nothing with numbers" in {
    assertResult(N(5.0)) {
      rename(N(5.0))
    }
  }
  "Rename" should "rename variables from an environment" in {
    assertResult((47,Var("x99"))) {
      rename(Map("a" -> "x99"), Var("a"))(47)
    }
  }
  "rename" should "not rename constant expressions" in {
    assertResult(Binary(Plus ,N(10), N(11))) {
      rename(Binary(Plus, N(10), N(11)))
    }
  }
  it should "rename operands in a sum" in {
    assertResult((47,Binary(Plus, Var("x99"), N(11)))) {
      rename(Map("a" -> "x99"), Binary(Plus, Var("a"), N(11)))(47)
    }
  }
  it should "create fresh variables and rename its scope" in  {
    assertResult((100, Decl(MConst, "x99", N(47), Var("x99")))) {
      rename(Map(), Decl(MConst, "a", N(47), Var("a")))(99)
    }
  }
}

class Lab5InterpreterSpec extends FlatSpec {

  "CastOkNull" should "perform CastOkNull" in {
    assertResult(true) {
      castOk(TNull, TObj(Map()))
    }
  }

  "DoNeg" should "return the negation of a number value without altering memory" in {
    val e1 = N(5)
    val e2 = Unary(Neg, e1)
    assertResult(N(-5)) {
      val (_, r) = step(e2)(memempty)
      r
    }
  }
  "DoCallName" should "sub in its body for ever use of its param, the expr arg" in {
    val v = Function(None, Right(PName, "x", TNumber),None, Binary(Seq, Var("x"), Var("x")))
    val e1 = Unary(Neg, N(47))
    val e2 = Call(v, List(e1))
    val m = memempty
    assertResult((m, Binary(Seq, e1, e1))){
      step(e2)(m)
    }
  }
}

class TypeCheckingSpec extends FlatSpec {
  "TNumber" should "type numbers to TNumber" in {
    assert(typeInfer(emp, N(47)) == TNumber)
  }
  "TString" should "type strings to TString" in {
    assert(typeInfer(emp, S("hi")) == TString)
  }
  "TBool" should "type booleans to TBool" in {
    assert(typeInfer(emp, B(true)) == TBool)
  }
  "TUndefined" should "type undefined to TUnderined" in {
    assert(typeInfer(emp, Undefined) == TUndefined)
  }
  "TypeNeg" should "type to TNumber" in {
    assert(typeInfer(emp, Unary(Neg, N(5))) == TNumber)
    intercept[StaticTypeError] {
      typeInfer(emp, Unary(Neg, B(true)))
    }
  }
  "TypeNot" should "type to TBool" in {
    assert(typeInfer(emp, Unary(Not, B(true))) == TBool)
    intercept[StaticTypeError] {
      typeInfer(emp, Unary(Not, N(5)))
    }
  }
  "TypeSeq" should "type to the second expression" in {
    assert(typeInfer(emp, Binary(Seq, N(1.0), B(true))) == TBool)
    intercept[StaticTypeError] {
      inferType(Binary(Seq, Binary(Plus, N(1), Undefined), N(3)))
    }
  }
  "TypeArith" should "type to TNumber so long as types agree" in {
    assert(typeInfer(emp, Binary(Plus, N(5), N(1))) == TNumber)
    assert(typeInfer(emp, Binary(Minus, N(5), N(1))) == TNumber)
    assert(typeInfer(emp, Binary(Times, N(5), N(1))) == TNumber)
    assert(typeInfer(emp, Binary(Div, N(5), N(1))) == TNumber)
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Plus, S("hi"), N(5)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Plus, N(1), S("hi")))
    }
  }
  "TypePlusStr" should "type to TString so long as types agree" in {
    assert(typeInfer(emp, Binary(Plus, S("hi"), S("bye"))) === TString)
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Plus, B(true), S("hi")))
    }
  }
  "TypeInequalityNum" should "type to TBool so long as types agree" in {
    assert(typeInfer(emp, Binary(Lt, N(5), N(3))) == TBool)
    assert(typeInfer(emp, Binary(Gt, N(5), N(3))) == TBool)
    assert(typeInfer(emp, Binary(Le, N(5), N(3))) == TBool)
    assert(typeInfer(emp, Binary(Ge, N(5), N(3))) == TBool)
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Lt, B(true), Undefined))
    }
  }
  "TypeInequalityStr" should "type to TBool so long as types agree" in {
    assert(typeInfer(emp, Binary(Lt, S("hi"), S("bye"))) == TBool)
    assert(typeInfer(emp, Binary(Gt, S("hi"), S("bye"))) == TBool)
    assert(typeInfer(emp, Binary(Le, S("hi"), S("bye"))) == TBool)
    assert(typeInfer(emp, Binary(Ge, S("hi"), S("bye"))) == TBool)
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Lt, B(true), B(false)))
    }
  }
  "TypeEquality" should "type to TBool so long as types agree and no functions" in {
    assert(inferType(Binary(Eq, B(true), B(false))) == TBool)
    assert(inferType(Binary(Ne, B(true), B(false))) == TBool)
    assert(inferType(Binary(Eq, N(5), N(7))) == TBool)
    assert(inferType(Binary(Ne, N(5), N(7))) == TBool)
    assert(inferType(Binary(Eq, S("hi"), S("bye"))) == TBool)
    assert(inferType(Binary(Ne, S("hi"), S("bye"))) == TBool)
    assert(inferType(Binary(Eq, Undefined, Undefined)) == TBool)
    intercept[StaticTypeError] {
      inferType(Binary(Ne, Undefined, N(5)))
    }
    intercept[StaticTypeError] {
      inferType(Binary(Eq, Function(None, Left(List(("x", TNumber))), None, Var("x")), N(5)))
    }
  }
  "TypeAndOr" should "type to TBool so long as types agree" in {
    assert(inferType(Binary(And, B(true), B(false))) == TBool)
    assert(inferType(Binary(Or, B(true), B(false))) == TBool)
    intercept[StaticTypeError] {
      inferType(Binary(And, B(true), Undefined))
    }
    intercept[StaticTypeError] {
      inferType(Binary(Or, Undefined, B(false)))
    }
  }
  "TypeIf" should "type to typ(e2) provided e1 = bool, and typ(e2)=typ(e3)" in {
    assert(inferType(If(B(true), N(5), N(1))) == TNumber)
    assert(inferType(If(B(false), N(5), N(2))) == TNumber)
    intercept[StaticTypeError] {
      inferType(If(Undefined, N(5), N(1)))
    }
    intercept[StaticTypeError] {
      inferType(If(B(true), N(5), S("hi")))
    }
  }
  "TypeGetField/TypeObject" should "check types of the fields of objects" in {
    val Object = Obj(Map("x" -> N(1), "y" -> N(2)))
    assertResult(TObj(Map("x" -> TNumber, "y" -> TNumber))) {
      typeInfer(emp, Object)
    }
    assertResult(TNumber) {
      typeInfer(emp, GetField(Object, "x"))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, GetField(Object, "z"))
    }
  }

}

  // Probably want to write some tests for castOk, typeInfer, substitute, and step.



// The next bit of code runs a test for each .jsy file in src/test/resources/lab4.
// The test expects a corresponding .ans file with the expected result.
class Lab5JsyTests extends JavascriptyTester(None, "lab5", Lab5)

class Lab5Suite extends Suites(
  new Lab5ExercisesSpec,
  new Lab5InterpreterSpec,
  new TypeCheckingSpec,
  new Lab5JsyTests
)