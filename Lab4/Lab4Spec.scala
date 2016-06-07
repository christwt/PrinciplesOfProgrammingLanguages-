import org.scalatest._
import jsy.tester.JavascriptyTester
import jsy.lab4.ast._
import jsy.lab4.Parser.parse

import jsy.student.Lab4
import Lab4._

class HigherOrderFunctionsExercisesSpec extends FlatSpec {

  "compressRec/compressFold" should "compress List(1, 2, 2, 3, 3, 3)" in {
    val l1 = List(1, 2, 2, 3, 3, 3)
    val gold1 = List(1, 2, 3)
    assertResult(gold1) { compressRec(l1) }
    assertResult(gold1) { compressFold(l1) }
  } 
  
  "mapFirst" should "map the first element where f returns Some" in {
     val l1 = List(1, 2, -3, 4, -5)
     val gold1 = List(1, 2, 3, 4, -5)
     assertResult(gold1) {
       mapFirst { (i: Int) => if (i < 0) Some(-i) else None } (l1)
     }
  }
  
  "foldLeft" should "enable implementing treeFromList and sum" in {
    assertResult(6){
      sum(treeFromList(List(1, 2, 3)))
    }
  }

  "strictlyOrdered" should "check strict ordering of a binary search tree" in {
    assert(!strictlyOrdered(treeFromList(List(1,1,2))))
    assert(strictlyOrdered(treeFromList(List(1,2))))
  } 
}

class TypeInferSpec extends FlatSpec {

  val xtype = TNumber
  val tenvx = extend(emp, "x", xtype)

  "TypeVar" should "perform TypeVar" in {
    assertResult(xtype) {
      typeInfer(tenvx, Var("x"))
    }
  }
  "TypeUnary" should "perform TypeUnary on numbers and booleans" in {
    assertResult(TNumber) {
      typeInfer(emp, Unary(Neg, N(1.0)))
    }
    assertResult(TBool) {
      typeInfer(emp, Unary(Not, B(false)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Unary(Neg, B(false)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Unary(Not, N(1.0)))
    }
  }
  "TypeBinaryPlus" should "perform TypeBinaryPlus on strings and numbers" in {
    assertResult(TNumber) {
      typeInfer(emp, Binary(Plus, N(1.0), N(2.0)))
    }
    assertResult(TString) {
      typeInfer(emp, Binary(Plus, S("hi"), S(" there")))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Binary( Plus, N(1.0), S("hi")))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Plus, Undefined, B(true)))
    }
  }
  "TypeBinaryArith" should "perform TypeBinaryArith on numbers only" in {
    assertResult(TNumber) {
      typeInfer(emp, Binary(Minus, N(1.0), N(2.0)))
    }
    assertResult(TNumber) {
      typeInfer(emp, Binary(Times, N(1.0), N(2.0)))
    }
    assertResult(TNumber) {
      typeInfer(emp, Binary(Div, N(1.0), N(2.0)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Div, N(1.0), S("hi")))
    }
  }
  "TypeEq|Ne" should "perform TypeEq|Ne on all types aside from functions and return TBool" in {
    assertResult(TBool) {
      typeInfer(emp, Binary(Ne, N(1.0), N(2.0)))
    }
    assertResult(TBool) {
      typeInfer(emp, Binary(Ne, S("hi"), S("there")))
    }
    assertResult(TBool) {
      typeInfer(emp, Binary(Eq, Undefined, Undefined))
    }
    assertResult(TBool) {
      typeInfer(emp, Binary(Ne, B(true), B(false)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Eq, N(1.0), B(false)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Ne, Function(None,List(("x",TNumber)),None,Var("x")), S("hi")))
    }
  }
  "TypeInequality" should "perform TypeInequality on numbers and string returning TBool" in {
    assertResult(TBool) {
      typeInfer(emp, Binary(Lt, N(1.0), N(2.0)))
    }
    assertResult(TBool) {
      typeInfer(emp, Binary(Gt, S("hi"), S("there")))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Gt, B(false), B(true)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(Gt, N(1.0), Undefined))
    }
  }
  "TypeAnd" should "perform TypeAnd on booleans" in {
    assertResult(TBool) {
      typeInfer(emp, Binary(And, B(true), B(false)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(And, N(1.0), N(0.0)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Binary(And, B(true), N(1.0)))
    }
  }
  "TypeIf" should "ensure that e1 == bool as well as ensure that type e2 == type e3" in {
    assertResult(TNumber) {
      typeInfer(emp, If(B(false), N(1), N(5)))
    }
    assertResult(TNumber) {
      typeInfer(emp, If(B(true), N(1), N(5)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, If(Undefined, N(1), N(5)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, If(B(true), N(1), B(false)))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, If(B(false), N(1), S("hi")))
    }
  }
  "TypeCall" should "ensure that call matched function params and args" in {
    assertResult(TUndefined) {
      typeInfer(emp, Call(Function(None, List(("x", TNumber), ("y", TBool)), None, Undefined), List(N(1), B(true))))
    }
    intercept[StaticTypeError] {
      typeInfer(emp, Call(Function(None, List(("x", TNumber), ("y", TBool)), None, Undefined), List(N(1), N(2))))
    }
  }
  "TypeCall2" should "check that call has the same number of params as args" in {
    intercept[StaticTypeError] {
      inferType(Call(Function(None, List(("x", TBool), ("y", TBool)), None, Undefined), List(B(true), B(false), B(true))))
    }
    intercept[StaticTypeError ] {
      typeInfer(emp,Call(Function(None, List(("x", TBool), ("y", TBool)), None, Undefined), List(B(true))))
    }
  }
  "TypeFunctionAnn" should "ensure that annotated functions return correct types" in {
    assertResult(TFunction(List(), TNumber)) {
      typeInfer(emp, Function(None, List(), Some(TNumber), N(1)))
    }
    intercept[StaticTypeError] {
      inferType(Function(None, List(), Some(TBool), N(1)))
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

  class SubstituteSpec extends FlatSpec {
    "subst" should "fully substitute and object." in {
      assertResult(Obj(Map("x" -> N(47), "y" -> Var("xyz")))) {
        substitute(Obj(Map("x" -> Var("abc"), "y" -> Var("xyz"))), N(47), "abc")
      }
    }
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

  class DoSpec extends FlatSpec {
    "DoUnary" should "perform final eval step" in {
      assertResult(N(-42)) {
        step(Unary(Neg, N(42)))
      }
      assertResult(B(false)) {
        step(Unary(Not, B(true)))
      }
    }
    "DoSeq" should "evaluate to the second expr" in {
      assertResult(Binary(Plus, N(42), N(1))) {
        step(Binary(Seq, N(1.0), Binary(Plus, N(42), N(1))))
      }
    }
    "DoArith" should "evaluate arithmetic expressions with vals" in {
      assertResult(N(47)) {
        step(Binary(Plus, N(42), N(5)))
      }
      assertResult(N(37)) {
        step(Binary(Minus, N(42), N(5)))
      }
      assertResult(N(15)) {
        step(Binary(Times, N(3), N(5)))
      }
      assertResult(N(5)) {
        step(Binary(Div, N(15), N(3)))
      }
    }
    "DoPlusString" should "concatenate 2 string vals" in {
      assertResult(S("hello there")) {
        step(Binary(Plus, S("hello"), S(" there")))
      }
    }
    "DoIneqNum" should "perform inequality on number vals" in {
      assertResult(B(false)) {
        step(Binary(Lt, N(15), N(5)))
      }
      assertResult(B(false)) {
        step(Binary(Le, N(15), N(5)))
      }
      assertResult(B(true)) {
        step(Binary(Gt, N(15), N(5)))
      }
      assertResult(B(true)) {
        step(Binary(Ge, N(15), N(5)))
      }
    }
    "DoIneqStr" should "perform inequality on string vals" in {
      assertResult(B(false)) {
        step(Binary(Lt, S("hi"), S("bye")))
      }
      assertResult(B(false)) {
        step(Binary(Le, S("hi"), S("bye")))
      }
      assertResult(B(true)) {
        step(Binary(Gt, S("hi"), S("bye")))
      }
      assertResult(B(true)) {
        step(Binary(Ge, S("hi"), S("bye")))
      }
    }
    "DoEq/Ne" should "perform comparison of all types aside from functions" in {
      assertResult(B(true)) {
        step(Binary(Eq, N(47), N(47)))
      }
      assertResult(B(false)) {
        step(Binary(Ne, N(47), N(47)))
      }
      assertResult(B(true)) {
        step(Binary(Eq, S("hi"), S("hi")))
      }
      assertResult(B(false)) {
        step(Binary(Ne, S("hi"), S("hi")))
      }
      assertResult(B(true)) {
        step(Binary(Eq, B(true), B(true)))
      }
      assertResult(B(false)) {
        step(Binary(Ne, B(true), B(true)))
      }
      assertResult(B(true)) {
        step(Binary(Eq, Undefined, Undefined))
      }
      assertResult(B(false)) {
        step(Binary(Ne, Undefined, Undefined))
      }
    }
    "DoAndTrue" should "return the second expr iff v1 == true" in {
      assertResult(Binary(Plus, N(1), N(42))) {
        step(Binary(And, B(true), Binary(Plus, N(1), N(42))))
      }
    }
    "DoAndFalse" should "return false iff v1 == false" in {
      assertResult(B(false)) {
        step(Binary(And, B(false), Binary(Plus, N(1), N(42))))
      }
    }
    "DoOrTrue" should "return true iff v1 == true" in {
      assertResult(B(true)) {
        step(Binary(Or, B(true), Binary(Plus, N(1), N(42))))
      }
    }
    "DoOrFalse" should "return second expr iff v1 == false" in {
      assertResult(Binary(Plus, N(1), N(42))) {
        step(Binary(Or, B(false), Binary(Plus, N(1), N(42))))
      }
    }
    //---DoPrint already given in implementation: don't need test for it.
    "DoIfTrue" should "return e2 if v1 == true" in {
      assertResult(Binary(Plus, N(1), N(42))) {
        step(If(B(true), Binary(Plus,N(1), N(42)), Binary(And, B(true), B(false))))
      }
    }
    "DoIfFalse" should "return e3 if v1 == false" in {
      assertResult(Binary(And, B(true), B(false))) {
        step(If(B(false), Binary(Plus,N(1), N(42)), Binary(And, B(true), B(false))))
      }
    }
    "DoConstDecl" should "subst value of x into e2" in {
      assertResult(Binary(Plus, N(2.0), N(5.0))){
        step(ConstDecl("x", N(2),Binary(Plus, Var("x"), N(5.0))))
      }
    }
    "DoCall" should "sub in all parameter/arg bindings in its body" in {
      assertResult(Binary(Plus, N(1), N(2))){
        step(Call(
          Function(None, List(("x", TNumber), ("y", TNumber)), None,
            Binary(Plus, Var("x"), Var("y"))),
          List(N(1), N(2))))
      }
    }
  }

  class SearchSpec extends FlatSpec {
    "SearchUnary" should "step to e1'" in {
      assertResult(Unary(Neg, N(42))) {
        step(Unary(Neg, Binary(Minus, N(47), N(5))))
      }
      assertResult(Unary(Not, B(false))) {
        step(Unary(Not, Binary(And, B(false), B(true))))
      }
    }
    "SearchBinary1" should "step to e1' before stepping e2" in {
      assertResult(Binary(Plus, N(47), Binary(Plus, N(6), N(3)))) {
        step(Binary(Plus, Binary(Plus, N(42), N(5)), Binary(Plus, N(6), N(3))))
      }
    }
    "SearchBinary2" should "step to e2' if e1 is a value" in {
      assertResult(Binary(Plus, N(47), N(9))) {
        step(Binary(Plus, N(47), Binary(Plus, N(6), N(3))))
      }
    }
    //---SearchPrint already implemented for us, don't need a test for it.
    "SearchIf" should "step to e1'" in {
      assertResult(If(B(false), Binary(Plus, N(5), N(2)), B(false))) {
        step(If(Binary(And, B(true), B(false)), Binary(Plus, N(5), N(2)), B(false)))
      }
    }
    "SearchConst" should "step to e1'" in {
      assertResult(ConstDecl("x", N(2),Binary(Plus, Var("x"), N(5.0)))){
        step(ConstDecl("x", Binary(Minus, N(5), N(3)), Binary(Plus, Var("x"), N(5.0))))
      }
    }
    "SearchObject" should "step its first non-value field" in {
      assertResult(Obj(Map("a" -> N(10), "b" -> N(-10), "c" -> Unary(Neg, N(42))))){
        step(Obj(Map("a" -> N(10), "b" -> Unary(Neg, N(10)), "c" -> Unary(Neg, N(42)))))
      }
    }
  }

class FunctionCallSpec extends FlatSpec {
  "Functions" should "be considered values" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, List((x, TNumber)), Some(TNumber), Var(x))
    val e2 = Function(Some(f), List((x, TNumber)), Some(TNumber), Var(x))
    assert(isValue(e1))
    assert(isValue(e2))
  }

  "Call" should "evaluate a function using small-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, List((x, TNumber)), Some(TNumber), Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = iterateStep(Call(e1, List(e2)))
    assert(e3 === N(3))
  }

  "Call" should "handle recursive functions using small-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), List(Binary(Minus, Var(x), N(1))))))
    val e1 = Function(Some(f), List((x, TNumber)), Some(TNumber), fbody)
    val e2 = N(3)
    val e3 = iterateStep(Call(e1, List(e2)))
    assert(e3 === N(6))
  }
}

// The next bit of code runs a test for each .jsy file in src/test/resources/lab4.
// The test expects a corresponding .ans file with the expected result.
class Lab4JsyTests extends JavascriptyTester(None, "lab4", Lab4)

class Lab4Suite extends Suites(
  new HigherOrderFunctionsExercisesSpec,
  new TypeInferSpec,
  new DoSpec,
  new SearchSpec,
  new FunctionCallSpec,
  new Lab4JsyTests
)