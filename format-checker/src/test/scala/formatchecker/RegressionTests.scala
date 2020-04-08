
package formatchecker;

import org.scalatest.FlatSpec
import collection.mutable.Stack

object RegressionTests {
  val PREFIX = "tests/"
}

class RegressionTests extends FlatSpec {
  import RegressionTests._

  def testFile(filename : String,
               general : Boolean = true,
               LIA : Boolean = false,
               LIALin : Boolean = false,
               LRA : Boolean = false,
               LRATS : Boolean = false,
               LIALinArrays : Boolean = false) = {
    filename should ((if (general) "" else "not ") + "parse") in {
      assert(Checker(Array(PREFIX + filename)) == general)
    }
    it should ((if (LIA) "be" else "not be") + " LIA") in {
      assert(LIAChecker(Array(PREFIX + filename)) == LIA)
    }
    it should ((if (LIALin) "be" else "not be") + " LIA-linear") in {
      assert(LIALinChecker(Array(PREFIX + filename)) == LIALin)
    }
    it should ((if (LRA) "be" else "not be") + " LRA") in {
      assert(LRAChecker(Array(PREFIX + filename)) == LRA)
    }
    it should ((if (LRATS) "be" else "not be") + " LRA-TS") in {
      assert(LRATSChecker(Array(PREFIX + filename)) == LRATS)
    }
    it should ((if (LIALin || LIALinArrays) "be" else "not be") + " LIA-Lin-Arrays") in {
      assert(LIALinArraysChecker(Array(PREFIX + filename)) == (LIALin || LIALinArrays))
    }
  }

  testFile("LIA-lin.smt2", LIA = true, LIALin = true)
  testFile("LIA-nonlin.smt2", LIA = true)
  testFile("LIA-bad-query-head.smt2", general = false)
  testFile("LIA-lin-mixed-types.smt2")
  testFile("reve.smt2", general = false)
  testFile("multi-queries.smt2", LIA = true, LIALin = true)

  testFile("chc-lra-0002.smt2", LRA = true, LRATS = true)
  testFile("chc-lia-lin-arr-0000-fixed.smt2", LIALinArrays = true)

  testFile("from-z3-script/cst_in_head.smt2", general = false)
  testFile("from-z3-script/distinct_vars.smt2", general = false)
  testFile("from-z3-script/multi_query.smt2", general = false)
  testFile("from-z3-script/query_not_last.smt2", general = false)
  testFile("from-z3-script/tail_is_not_conj.smt2", LIA = true, LIALin = true)
  testFile("from-z3-script/uf_in_iformula_1.smt2", general = false)
  testFile("from-z3-script/uf_in_iformula_2.smt2", general = false)
}
