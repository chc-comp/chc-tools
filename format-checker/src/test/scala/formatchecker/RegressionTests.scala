
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
  }

  testFile("LIA-lin.smt2", LIA = true, LIALin = true)
  testFile("LIA-lin-mixed-types.smt2")
  testFile("reve.smt2", general = false)
}