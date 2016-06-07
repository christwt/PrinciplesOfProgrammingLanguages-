import org.scalatest._
import jsy.tester.JavascriptyTester

import jsy.lab6.ast._
import jsy.student.Lab6
import Lab6._

import scala.util.matching.Regex
import scala.util.parsing.input.CharSequenceReader

object Lab6Harness {

  def regExprToRegex(re: RegExpr): Regex = {
    def toR(re: RegExpr): String = re match {
      case REmptyString => ""
      case RSingle(c) => c.toString
      case RConcat(re1, re2) => toR(re1) + toR(re2)
      case RUnion(re1, re2) => s"(${toR(re1)}|${toR(re2)})"
      case RStar (re1) => s"(${toR(re1)})*"
      case RAnyChar => "."
      case RPlus(re1) => s"(${toR(re1)})+"
      case ROption(re1) => s"(${toR(re1)})?"
      case _ => throw new IllegalArgumentException(s"Unsupported RegExpr ${re}")
    }
    new Regex(raw"\A" + toR(re) + raw"\z")
  }

  def retestRegex(re: Regex, str: String): Boolean =
    !re.findPrefixOf(str).isEmpty

}
class RegExprUnitSpec extends FlatSpec {
  "RSingle" should "result after parsing a single char" in {
    assertResult(RSingle('a')) {
      REParser.atom(new CharSequenceReader("a"))
      REParser.parse(new CharSequenceReader("a"))
      REParser.parse("a")
    }
  }
}

class RegExprMatcherSPec extends FlatSpec {
  "RNoString" should "not match EVER" in {
    assert(!retest(RNoString, ""))
    assert(!retest(RNoString, "foo"))
    //using val for tests.
    val re = RNoString
    assert(!retest(re, ""))
    assert(!retest(re,"a"))
    assert(!retest(re,"ab"))
  }

  "REmptyString" should "match the empty string" in {
    assert(!retest(REmptyString, "foo"))
    assert(retest(REmptyString, ""))
    //using val for tests.
    val re = REmptyString
    assert(retest(re, ""))
    assert(!retest(re, "a"))
    assert(!retest(re, "ab"))
  }

  "RSingle" should "only match a single char" in {
    assert(!retest(RSingle('c'),"cd"))
    assert(!retest(RSingle('c'), ""))
    assert(retest(RSingle('c'), "c"))
  }

  "RConcat" should "match a concat of two regexs" in {
    val re = RConcat(RSingle('a'), RSingle('b')) // /ab/
    assert(!retest(re, ""))
    assert(!retest(re, "a"))
    assert(!retest(re, "c"))
    assert(!retest(re, "abc"))
    assert(retest(re, "ab"))

  }

  "RUnion" should "match alternatives" in {
    assert(retest(RUnion(RSingle('a'), RSingle('b')), "a"))
    val re = RUnion(RSingle('a'), RSingle('b'))
    assert(!retest(re, "c"))
    assert(!retest(re, "ab"))
    assert(retest(re, "b"))
    assert(retest(re, "a"))
  }

  "RStar" should "match 0 to one concatenations of re1" in {
    val re = RStar(RSingle('a'))
    assert(!retest(re, "ab"))
    assert(retest(re, "aa"))
  }

  "RAnyChar" should "match string containing a single char" in {
    assert(!retest(RAnyChar, "cbd"))
    assert(retest(RAnyChar, "x"))
  }

  "RPlus" should "match zero to one concatenations of re1" in {
  }

  "ROption" should "match zero or one matches of re1" in {
}

class RegExParserSpec extends FlatSpec {
  "atom" should "match an atom on input" in {

  }
}

class RegExprSpec extends FlatSpec {
  import Lab6Harness._

  val strings = List(
     "",
     "a",
     "aa",
     "ab",
     "aaa"
  )

  val respecs = List(
    "a",
    "b",
    ".",
    "aa",
    "(aa)*"
  )
  
  val respecsast = respecs map { s => jsy.lab6.RegExprParser.parse(s) }


  behavior of "parse"

  for ((restr,re) <- (respecs,respecsast).zipped) {
    it should s"on '${restr}' produce a RegExpr AST matching the reference" in {
      assertResult(re) { REParser.parse(restr)}
    }
  }


  behavior of "retest"

  // Note that this testing uses Scala's regular expression matcher, which does not
  // support !, &, or ~.
  for (re <- respecsast) {
    for (s <- strings) {
      it should s"test '${s}' on '${pretty(re)}'" in {
        val regex = regExprToRegex(re)
        assertResult(retestRegex(regex, s)) { retest(re, s) }
      }
    }
  }
  
}

// The next bit of code runs a test for each .jsy file in src/test/resources/lab4.
// The test expects a corresponding .ans file with the expected result.
class Lab6JsyTests extends JavascriptyTester(None, "lab6", Lab6)

class Lab6Suite extends Suites(
  new RegExprSpec,
  new RegExParserSpec,
  new Lab6JsyTests
)