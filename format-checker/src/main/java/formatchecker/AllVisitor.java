package formatchecker;

import ap.parser.smtlib.Absyn.*;

/** BNFC-Generated All Visitor */
public interface AllVisitor<R,A> extends
  ap.parser.smtlib.Absyn.ScriptC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.Command.Visitor<R,A>,
  ap.parser.smtlib.Absyn.OptionC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.Sort.Visitor<R,A>,
  ap.parser.smtlib.Absyn.MESorts.Visitor<R,A>,
  ap.parser.smtlib.Absyn.ConstructorDeclC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.SelectorDeclC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.PolySortC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.MaybeParDataDecl.Visitor<R,A>,
  ap.parser.smtlib.Absyn.OldDataDeclC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.Term.Visitor<R,A>,
  ap.parser.smtlib.Absyn.BindingC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.Quantifier.Visitor<R,A>,
  ap.parser.smtlib.Absyn.SymbolRef.Visitor<R,A>,
  ap.parser.smtlib.Absyn.FunSignatureC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.SortedVariableC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.ESortedVarC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.SpecConstant.Visitor<R,A>,
  ap.parser.smtlib.Absyn.MetaConstant.Visitor<R,A>,
  ap.parser.smtlib.Absyn.Identifier.Visitor<R,A>,
  ap.parser.smtlib.Absyn.IndexC.Visitor<R,A>,
  ap.parser.smtlib.Absyn.Symbol.Visitor<R,A>,
  ap.parser.smtlib.Absyn.Annotation.Visitor<R,A>,
  ap.parser.smtlib.Absyn.AttrParam.Visitor<R,A>,
  ap.parser.smtlib.Absyn.SExpr.Visitor<R,A>
{}
