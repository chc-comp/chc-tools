package formatchecker;

import ap.parser.smtlib.Absyn.*;
import java.util.Collections;
import java.util.List;
import java.util.ArrayList;

/** BNFC-Generated Fold Visitor */
public abstract class FoldVisitor<R,A> implements AllVisitor<R,A> {
    public abstract R leaf(A arg);
    public abstract R combine(R x, R y, A arg);

/* ScriptC */
    public R visit(ap.parser.smtlib.Absyn.Script p, A arg) {
      R r = leaf(arg);
      for (Command x : p.listcommand_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* Command */
    public R visit(ap.parser.smtlib.Absyn.SetLogicCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.SetOptionCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.optionc_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.SetInfoCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.annotation_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.SortDeclCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.SortDefCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      for (Symbol x : p.listsymbol_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      r = combine(p.sort_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.DataDeclsCommand p, A arg) {
      R r = leaf(arg);
      for (PolySortC x : p.listpolysortc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      for (MaybeParDataDecl x : p.listmaybepardatadecl_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.DataDeclsOldCommand p, A arg) {
      R r = leaf(arg);
      for (Symbol x : p.listsymbol_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      for (OldDataDeclC x : p.listolddatadeclc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.DataDeclCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      for (ConstructorDeclC x : p.listconstructordeclc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.FunctionDeclCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      r = combine(p.mesorts_.accept(this, arg), r, arg);
      r = combine(p.sort_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.ConstDeclCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      r = combine(p.sort_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.FunctionDefCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      for (ESortedVarC x : p.listesortedvarc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      r = combine(p.sort_.accept(this, arg), r, arg);
      r = combine(p.term_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.ConstDefCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      r = combine(p.sort_.accept(this, arg), r, arg);
      r = combine(p.term_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.RecFunctionDefCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      for (ESortedVarC x : p.listesortedvarc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      r = combine(p.sort_.accept(this, arg), r, arg);
      r = combine(p.term_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.RecFunctionDefsCommand p, A arg) {
      R r = leaf(arg);
      for (FunSignatureC x : p.listfunsignaturec_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      for (Term x : p.listterm_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.PushCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.PopCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.AssertCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.term_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.CheckSatCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.GetAssertionsCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.GetValueCommand p, A arg) {
      R r = leaf(arg);
      for (Term x : p.listterm_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.SimplifyCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.term_.accept(this, arg), r, arg);
      return r;
    }
    /*WARNING: this is just a stub to make compiler happy. TODO: Implement*/
    public R visit(ap.parser.smtlib.Absyn.HeapDeclCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.GetProofCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.GetUnsatCoreCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.GetAssignmentCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.GetModelCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.GetInterpolantsCommand p, A arg) {
      R r = leaf(arg);
      for (SExpr x : p.listsexpr_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.GetInfoCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.GetOptionCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.EchoCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.ResetCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.ExitCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.IgnoreCommand p, A arg) {
      R r = leaf(arg);
      r = combine(p.term_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.EmptyCommand p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* OptionC */
    public R visit(ap.parser.smtlib.Absyn.Option p, A arg) {
      R r = leaf(arg);
      r = combine(p.annotation_.accept(this, arg), r, arg);
      return r;
    }

/* Sort */
    public R visit(ap.parser.smtlib.Absyn.IdentSort p, A arg) {
      R r = leaf(arg);
      r = combine(p.identifier_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.CompositeSort p, A arg) {
      R r = leaf(arg);
      r = combine(p.identifier_.accept(this, arg), r, arg);
      for (Sort x : p.listsort_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* MESorts */
    public R visit(ap.parser.smtlib.Absyn.SomeSorts p, A arg) {
      R r = leaf(arg);
      for (Sort x : p.listsort_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.NoSorts p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* ConstructorDeclC */
    public R visit(ap.parser.smtlib.Absyn.NullConstructorDecl p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.ConstructorDecl p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      for (SelectorDeclC x : p.listselectordeclc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* SelectorDeclC */
    public R visit(ap.parser.smtlib.Absyn.SelectorDecl p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      r = combine(p.sort_.accept(this, arg), r, arg);
      return r;
    }

/* PolySortC */
    public R visit(ap.parser.smtlib.Absyn.PolySort p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      return r;
    }

/* MaybeParDataDecl */
    public R visit(ap.parser.smtlib.Absyn.MonoDataDecl p, A arg) {
      R r = leaf(arg);
      for (ConstructorDeclC x : p.listconstructordeclc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.ParDataDecl p, A arg) {
      R r = leaf(arg);
      for (Symbol x : p.listsymbol_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      for (ConstructorDeclC x : p.listconstructordeclc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* OldDataDeclC */
    public R visit(ap.parser.smtlib.Absyn.OldDataDecl p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      for (ConstructorDeclC x : p.listconstructordeclc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* Term */
    public R visit(ap.parser.smtlib.Absyn.ConstantTerm p, A arg) {
      R r = leaf(arg);
      r = combine(p.specconstant_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.NullaryTerm p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbolref_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.FunctionTerm p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbolref_.accept(this, arg), r, arg);
      for (Term x : p.listterm_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.LetTerm p, A arg) {
      R r = leaf(arg);
      for (BindingC x : p.listbindingc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      r = combine(p.term_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.QuantifierTerm p, A arg) {
      R r = leaf(arg);
      r = combine(p.quantifier_.accept(this, arg), r, arg);
      for (SortedVariableC x : p.listsortedvariablec_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      r = combine(p.term_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.AnnotationTerm p, A arg) {
      R r = leaf(arg);
      r = combine(p.term_.accept(this, arg), r, arg);
      for (Annotation x : p.listannotation_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* BindingC */
    public R visit(ap.parser.smtlib.Absyn.Binding p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      r = combine(p.term_.accept(this, arg), r, arg);
      return r;
    }

/* Quantifier */
    public R visit(ap.parser.smtlib.Absyn.AllQuantifier p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.ExQuantifier p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.EpsQuantifier p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.LbdQuantifier p, A arg) {
      R r = leaf(arg);
      return r;
    }
/* SymbolRef */
    public R visit(ap.parser.smtlib.Absyn.IdentifierRef p, A arg) {
      R r = leaf(arg);
      r = combine(p.identifier_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.CastIdentifierRef p, A arg) {
      R r = leaf(arg);
      r = combine(p.identifier_.accept(this, arg), r, arg);
      r = combine(p.sort_.accept(this, arg), r, arg);
      return r;
    }

/* FunSignatureC */
    public R visit(ap.parser.smtlib.Absyn.FunSignature p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      for (ESortedVarC x : p.listesortedvarc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      r = combine(p.sort_.accept(this, arg), r, arg);
      return r;
    }

/* SortedVariableC */
    public R visit(ap.parser.smtlib.Absyn.SortedVariable p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      r = combine(p.sort_.accept(this, arg), r, arg);
      return r;
    }

/* ESortedVarC */
    public R visit(ap.parser.smtlib.Absyn.ESortedVar p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      r = combine(p.sort_.accept(this, arg), r, arg);
      return r;
    }

/* SpecConstant */
    public R visit(ap.parser.smtlib.Absyn.NumConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.RatConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.HexConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.BinConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.StringConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.StringSQConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* MetaConstant */
    public R visit(ap.parser.smtlib.Absyn.NumMetaConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.RatMetaConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.HexMetaConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.BinMetaConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.StringMetaConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* Identifier */
    public R visit(ap.parser.smtlib.Absyn.SymbolIdent p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.IndexIdent p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      for (IndexC x : p.listindexc_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* IndexC */
    public R visit(ap.parser.smtlib.Absyn.NumIndex p, A arg) {
      R r = leaf(arg);
      return r;
    }

    public R visit(ap.parser.smtlib.Absyn.SymIndex p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* Symbol */
    public R visit(ap.parser.smtlib.Absyn.NormalSymbol p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.QuotedSymbol p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* Annotation */
    public R visit(ap.parser.smtlib.Absyn.AttrAnnotation p, A arg) {
      R r = leaf(arg);
      r = combine(p.attrparam_.accept(this, arg), r, arg);
      return r;
    }

/* AttrParam */
    public R visit(ap.parser.smtlib.Absyn.SomeAttrParam p, A arg) {
      R r = leaf(arg);
      r = combine(p.sexpr_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.NoAttrParam p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* SExpr */
    public R visit(ap.parser.smtlib.Absyn.ConstantSExpr p, A arg) {
      R r = leaf(arg);
      r = combine(p.specconstant_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.SymbolSExpr p, A arg) {
      R r = leaf(arg);
      r = combine(p.symbol_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(ap.parser.smtlib.Absyn.ParenSExpr p, A arg) {
      R r = leaf(arg);
      for (SExpr x : p.listsexpr_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }


}
