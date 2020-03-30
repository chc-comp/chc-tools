
package formatchecker;

import ap.parser.smtlib._
import ap.parser.smtlib.Absyn._

import scala.{Option => SOption}
import scala.collection.JavaConverters._

/**
 * Verify that an SMT-LIB script is in the CHC-COMP fragment.
 */
class AbstractChecker {

  val printer = new PrettyPrinterNonStatic

  def main(args: Array[String]) : Unit =
    for (filename <- args) try {
      Console.err.println("Checking \"" + filename + "\" ...")

      val input =
        new java.io.BufferedReader (
          new java.io.FileReader(new java.io.File (filename)))
      val l = new Yylex(input)
      val p = new parser(l) {
        override def report_error(message : String, info : Object) : Unit = {
          Console.err.println(message)
        }
      }

      val script = p.pScriptC

//      println(printer print script)
      val res = Script check script
      if (!res)
        System exit 1
    } catch {
      case t : Exception => println("ERROR: " + t.getMessage)
    }

  //////////////////////////////////////////////////////////////////////////////

  trait SMTLIBElement {
    def check(t : AnyRef) : Boolean

    lazy val asSeq = new SMTLIBElementSeq {
      def checkList(t : List[AnyRef]) : Either[List[AnyRef], Int] = t match {
        case s :: rest if check(s) => Left(rest)
        case _                     => Right(0)
      }
    }

    def |(that : SMTLIBElement) = {
      val sthis = this
      new SMTLIBElement {
        def check(t : AnyRef) : Boolean = sthis.check(t) || that.check(t)
      }
    }
  }

  object AnySMTLIBElement extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = true
  }

  //////////////////////////////////////////////////////////////////////////////

  trait SMTLIBElementSeq {
    /**
     * Check whether a prefix of the given list is accepted; return
     * either the remaining suffix, or the index at which checking
     * failed.
     */
    def checkList(t : List[AnyRef]) : Either[List[AnyRef], Int]

    def checkJavaList[A <: AnyRef](t : java.util.List[A]) : Boolean =
      checkList(t.asScala.toList) == Left(List())

    def ++(that : SMTLIBElementSeq) : SMTLIBElementSeq = {
      val sthis = this
      new SMTLIBElementSeq {
        def checkList(t : List[AnyRef]) : Either[List[AnyRef], Int] =
          sthis.checkList(t) match {
            case Left(rest) =>
              that.checkList(rest) match {
                case l@Left(_) => l
                case Right(n)  => Right(n + t.size - rest.size)
              }
            case r@Right(_) =>
              r
          }
      }
    }

    def * : SMTLIBElementSeq = {
      val sthis = this
      new SMTLIBElementSeq {
        def checkList(t : List[AnyRef]) : Either[List[AnyRef], Int] = {
          var r = t
          while (!r.isEmpty)
            sthis.checkList(r) match {
              case Left(r2) => r = r2
              case Right(n) => return Left(r)
            }
          Left(r)
        }
      }
    }

    def + : SMTLIBElementSeq =
      this ++ this.*

    def ? : SMTLIBElementSeq = {
      val sthis = this
      new SMTLIBElementSeq {
        def checkList(t : List[AnyRef]) : Either[List[AnyRef], Int] =
          sthis.checkList(t) match {
            case Left(r)  => Left(r)
            case Right(_) => Left(t)
          }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  object Script extends SMTLIBElement {
    val commands = SetInfo.asSeq.* ++
                   SetLogic.asSeq ++
                   SetInfo.asSeq.* ++
                   FunDecl.asSeq.* ++
                   CHCAssert.asSeq.* ++
                   CHCQuery.asSeq ++
                   CheckSat.asSeq ++
                   Exit.asSeq.?

    def check(t : AnyRef) : Boolean = t match {
      case t : Script =>
        commands.checkList(t.listcommand_.asScala.toList) match {
          case Left(List()) => {
            println("passed")
            true
          }
          case Left(r :: _) => {
            println("unexpected command: " +
                    (printer print r.asInstanceOf[Command]))
            false
          }
          case Right(n) => {
            println("could not parse command: " +
                    (printer print t.listcommand_.get(n).asInstanceOf[Command]))
            false
          }
        }
      case _ =>
        false
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  object SetLogic extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : SetLogicCommand =>
        (printer print c.symbol_) == "HORN"
      case _ =>
        false
    }
  }

  object SetInfo extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : SetInfoCommand =>
        true
      case _ =>
        false
    }
  }

  object CheckSat extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : CheckSatCommand =>
        true
      case _ =>
        false
    }
  }

  object Exit extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : ExitCommand =>
        true
      case _ =>
        false
    }
  }

  object FunDecl extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : FunctionDeclCommand =>
        (printer print c.sort_) == "Bool" &&
        (c.mesorts_ match {
           case d : SomeSorts =>
             AcceptedSort.asSeq.* checkJavaList d.listsort_
           case _ : NoSorts =>
             true
         })
      case _ =>
        false
    }
  }

  val AcceptedSort : SMTLIBElement = AnySMTLIBElement

  case class FunExpression(op : String,
                           argsCheck : SMTLIBElementSeq) extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : FunctionTerm =>
        (printer print c.symbolref_) == op &&
        (argsCheck checkJavaList c.listterm_)
      case _ =>
        false
    }
  }

  object VarExpression extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : NullaryTerm =>
        c.symbolref_ match {
          case _ : IdentifierRef => true
          case _ => false
        }
      case _ =>
        false
    }
  }

  case class CHCClause(headCheck : SMTLIBElement) extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : AssertCommand =>
        c.term_ match {
          case f : QuantifierTerm =>
            (printer print f.quantifier_) == "forall" &&
            VarDecl.asSeq.+.checkJavaList(f.listsortedvariablec_) &&
            FunExpression("=>", CHCTail.asSeq ++ headCheck.asSeq).check(f.term_)
          case _ =>
            false
        }
      case _ =>
        false
    }
  }

  val CHCAssertClause = CHCClause(CHCHead)

  object CHCAssertFact extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : AssertCommand =>
        CHCHead check c.term_ // TODO: does not seem to make much sense
      case _ =>
        false
    }
  }

  val CHCAssert = CHCAssertClause | CHCAssertFact

  val CHCQuery = CHCClause(FalseFormula)

  object VarDecl extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : SortedVariable =>
        AcceptedSort.check(c.sort_)
      case _ =>
        false
    }
  }

  object CHCHead extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : FunctionTerm =>
        PredAtom.check(t) &&
        // distinct argument variables
        (for (t <- c.listterm_.asScala.iterator)
         yield (printer print t)).toSet.size == c.listterm_.size
      case _ =>
        false
    }
  }

  object PredAtom extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : FunctionTerm =>
        VarExpression.asSeq.*.checkJavaList(c.listterm_)
      case _ =>
        false
    }
  }

  object InterpretedFormula extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case t : FunctionTerm =>
        InterpretedFormulaVisitor.visit(t, ())
      case t : LetTerm =>
        InterpretedFormulaVisitor.visit(t, ())
      case _ =>
        true
    }
  }

  object FalseFormula extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : NullaryTerm =>
        (printer print c) == "false"
      case _ =>
        false
    }
  }

  val CHCTail = PredAtom |
                InterpretedFormula |
                FunExpression("and",
                              PredAtom.asSeq.* ++ InterpretedFormula.asSeq.*)

  //////////////////////////////////////////////////////////////////////////////

  val interpretedFunctions =
    Set("not", "and", "or", "=>",
        "ite",
        "=", "<", ">", "<=", ">=",
        "+", "-", "*", "mod", "div")

  object InterpretedFormulaVisitor extends FoldVisitor[Boolean, Unit] {
    def leaf(arg : Unit) = true
    def combine(x : Boolean, y : Boolean, arg : Unit) = x && y
    override def visit(p : FunctionTerm, arg : Unit) = {
      if (!(interpretedFunctions contains (printer print p.symbolref_))) {
//        println("did not recognise as interpreted: " + (printer print p))
        false
      } else {
        super.visit(p, arg)
      }
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

object Checker extends AbstractChecker

class AbstractLIAChecker extends AbstractChecker {

  val possibleSorts = Set("Int", "Bool")

  override val AcceptedSort : SMTLIBElement = new SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case s : Sort =>
        possibleSorts contains (printer print s)
      case _ =>
        false
    }
  }

}

object LIAChecker extends AbstractLIAChecker

object LIALinChecker extends AbstractLIAChecker {

  override val CHCTail =
    PredAtom |
    InterpretedFormula |
    FunExpression("and",
                  PredAtom.asSeq.? ++ InterpretedFormula.asSeq.*)

}
