
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

  def apply(args: Array[String]) : Boolean = {
    var result = true

    for (filename <- args) try {
      if (filename == "--strict") {
        useStrictMode = true
      } else {

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
        result = Script check script
      }
    } catch {
      case t : Exception => {
        println("ERROR: " + t.getMessage)
        result = false
      }
    }

    result
  }

  def main(args: Array[String]) : Unit =
    System exit (if (apply(args)) 0 else 1)

  private var useStrictMode = false

  def strictMode : Boolean = useStrictMode

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

  object EmptySMTLIBElementSeq extends SMTLIBElementSeq {
    def checkList(t : List[AnyRef]) : Either[List[AnyRef], Int] = Left(t)
  }

  //////////////////////////////////////////////////////////////////////////////

  def commandSequence = {
    setInfoSeq ++
    SetLogic.asSeq ++
    setInfoSeq ++
    FunDecl.asSeq.* ++
    (CHCAssertClause | CHCAssertFact).asSeq.* ++
    CHCQuery.asSeq ++
    CheckSat.asSeq ++
    exitSeq
  }

  def setInfoSeq =
    if (strictMode)
      EmptySMTLIBElementSeq
    else
      SetInfo.asSeq.*

  def exitSeq =
    if (strictMode)
      EmptySMTLIBElementSeq
    else
      Exit.asSeq.?

  object Script extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case t : Script =>
        commandSequence.checkList(t.listcommand_.asScala.toList) match {
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

  case class CHCClause(tailCheck: SMTLIBElement,
                       headCheck : SMTLIBElement) extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : AssertCommand =>
        c.term_ match {
          case f : QuantifierTerm =>
            (printer print f.quantifier_) == "forall" &&
            VarDecl.asSeq.+.checkJavaList(f.listsortedvariablec_) &&
            FunExpression("=>", tailCheck.asSeq ++ headCheck.asSeq).check(f.term_)
          case _ =>
            false
        }
      case _ =>
        false
    }
  }

  object CHCAssertFact extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : AssertCommand =>
        if (strictMode)
          CHCHead check c.term_ // TODO: does not seem to make much sense
        else
          c.term_ match {
            case f : QuantifierTerm =>
              (printer print f.quantifier_) == "forall" &&
              VarDecl.asSeq.+.checkJavaList(f.listsortedvariablec_) &&
              (CHCHead check f.term_)
            case f : NullaryTerm =>
              true
            case _ =>
              false
          }
      case _ =>
        false
    }
  }

  object VarDecl extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : SortedVariable =>
        AcceptedSort.check(c.sort_)
      case _ =>
        false
    }
  }

  object CHCHead extends SMTLIBElement {
    def check(t : AnyRef) : Boolean =
      (PredAtom check t) &&
      (t match {
       case c : FunctionTerm =>
         // distinct argument variables
         (for (t <- c.listterm_.asScala.iterator)
          yield (printer print t)).toSet.size == c.listterm_.size
       case _ =>
         true
     })
  }

  object PredAtom extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case c : FunctionTerm =>
        !(interpretedFunctions contains (printer print c.symbolref_)) &&
        VarExpression.asSeq.*.checkJavaList(c.listterm_)
      case c : NullaryTerm
          if !strictMode &&
             !(interpretedFunctions contains (printer print c)) =>
        true
      case _ =>
        false
    }
  }

  // TODO: check that is currently missing: no uninterpreted nullary
  // predicates occur in the formula 
  object InterpretedFormula extends SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case t : FunctionTerm =>
        InterpretedFormulaVisitor.visit(t, ())
      case t : NullaryTerm =>
        interpretedFunctions contains (printer print t)
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

  //////////////////////////////////////////////////////////////////////////////

  val CHCTail = PredAtom |
                InterpretedFormula |
                FunExpression("and",
                              PredAtom.asSeq.* ++ InterpretedFormula.asSeq.*)

  val CHCAssertClause = CHCClause(CHCTail, CHCHead)

  val CHCLinTail = PredAtom |
                   InterpretedFormula |
                   FunExpression("and",
                                 PredAtom.asSeq ++ InterpretedFormula.asSeq.*)

  val CHCLinAssertClause = CHCClause(CHCLinTail, CHCHead)

  val CHCAssertQuantifiedFact = CHCClause(InterpretedFormula, CHCHead)

  val CHCQuery = CHCClause(CHCTail, FalseFormula)

  val CHCLinQuery = CHCClause(CHCLinTail, FalseFormula)

  //////////////////////////////////////////////////////////////////////////////

  val interpretedFunctions =
    Set("not", "and", "or", "=>", "true", "false",
        "ite",
        "=", "distinct", "<", ">", "<=", ">=",
        "+", "-", "*", "mod", "div", "abs", "/", // "to_real", "to_int",
        "select", "store")

  object InterpretedFormulaVisitor extends FoldVisitor[Boolean, Unit] {
    def leaf(arg : Unit) = true
    def combine(x : Boolean, y : Boolean, arg : Unit) = x && y
    override def visit(p : FunctionTerm, arg : Unit) = {
      p.symbolref_ match {
//        case r : CastIdentifierRef if (printer print r.identifier_) == "const" =>
//          super.visit(p, arg)
        case r if (interpretedFunctions contains (printer print r)) =>
          super.visit(p, arg)
        case _ => {
//          println("did not recognise as interpreted: " + (printer print p))
          false
        }
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

abstract class AbstractLIALinChecker extends AbstractLIAChecker {

  override def commandSequence = {
    setInfoSeq ++
    SetLogic.asSeq ++
    setInfoSeq ++
    FunDecl.asSeq.* ++
    (CHCLinAssertClause | CHCAssertFact).asSeq.* ++
    CHCLinQuery.asSeq ++
    CheckSat.asSeq ++
    exitSeq
  }

}

object LIALinChecker extends AbstractLIALinChecker

object LIALinArraysChecker extends AbstractLIALinChecker {

  override val possibleSorts = Set("Int", "Bool", "(Array Int Int)")

}

object LIAArraysChecker extends AbstractLIAChecker {

  override val possibleSorts = Set("Int", "Bool", "(Array Int Int)")

}

////////////////////////////////////////////////////////////////////////////////

class AbstractLRAChecker extends AbstractChecker {

  val possibleSorts = Set("Real", "Bool")

  override val AcceptedSort : SMTLIBElement = new SMTLIBElement {
    def check(t : AnyRef) : Boolean = t match {
      case s : Sort =>
        possibleSorts contains (printer print s)
      case _ =>
        false
    }
  }

}

object LRAChecker extends AbstractLRAChecker

object LRALinChecker extends AbstractLIAChecker {

  override def commandSequence = {
    setInfoSeq ++
    SetLogic.asSeq ++
    setInfoSeq ++
    FunDecl.asSeq.* ++
    (CHCLinAssertClause | CHCAssertFact).asSeq.* ++
    CHCLinQuery.asSeq ++
    CheckSat.asSeq ++
    exitSeq
  }

}

object LRATSChecker extends AbstractLRAChecker {

  override def commandSequence = {
    setInfoSeq ++
    SetLogic.asSeq ++
    setInfoSeq ++
    FunDecl.asSeq ++
    (CHCAssertQuantifiedFact | CHCAssertFact).asSeq ++
    CHCLinAssertClause.asSeq ++
    CHCLinQuery.asSeq ++
    CheckSat.asSeq ++
    exitSeq
  }

}
