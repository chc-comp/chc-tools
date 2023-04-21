package formatchecker;
import ap.parser.smtlib.Absyn.*;
/** BNFC-Generated Abstract Visitor */
public class AbstractVisitor<R,A> implements AllVisitor<R,A> {
/* ScriptC */
    public R visit(ap.parser.smtlib.Absyn.Script p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.ScriptC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Command */
    public R visit(ap.parser.smtlib.Absyn.SetLogicCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.SetOptionCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.SetInfoCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.SortDeclCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.SortDefCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.DataDeclsCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.DataDeclsOldCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.DataDeclCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.FunctionDeclCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.ConstDeclCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.FunctionDefCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.ConstDefCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.RecFunctionDefCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.RecFunctionDefsCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.PushCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.PopCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.AssertCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.CheckSatCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.GetAssertionsCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.GetValueCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.SimplifyCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.HeapDeclCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.GetProofCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.GetUnsatCoreCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.GetAssignmentCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.GetModelCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.GetInterpolantsCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.GetInfoCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.GetOptionCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.EchoCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.ResetCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.ExitCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.IgnoreCommand p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.EmptyCommand p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.Command p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* OptionC */
    public R visit(ap.parser.smtlib.Absyn.Option p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.OptionC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Sort */
    public R visit(ap.parser.smtlib.Absyn.IdentSort p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.CompositeSort p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.Sort p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* MESorts */
    public R visit(ap.parser.smtlib.Absyn.SomeSorts p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.NoSorts p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.MESorts p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* ConstructorDeclC */
    public R visit(ap.parser.smtlib.Absyn.NullConstructorDecl p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.ConstructorDecl p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.ConstructorDeclC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* SelectorDeclC */
    public R visit(ap.parser.smtlib.Absyn.SelectorDecl p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.SelectorDeclC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* PolySortC */
    public R visit(ap.parser.smtlib.Absyn.PolySort p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.PolySortC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* MaybeParDataDecl */
    public R visit(ap.parser.smtlib.Absyn.MonoDataDecl p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.ParDataDecl p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.MaybeParDataDecl p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* OldDataDeclC */
    public R visit(ap.parser.smtlib.Absyn.OldDataDecl p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.OldDataDeclC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Term */
    public R visit(ap.parser.smtlib.Absyn.ConstantTerm p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.NullaryTerm p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.FunctionTerm p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.LetTerm p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.QuantifierTerm p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.AnnotationTerm p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.Term p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* BindingC */
    public R visit(ap.parser.smtlib.Absyn.Binding p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.BindingC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Quantifier */
    public R visit(ap.parser.smtlib.Absyn.AllQuantifier p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.ExQuantifier p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.EpsQuantifier p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.LbdQuantifier p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.Quantifier p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* SymbolRef */
    public R visit(ap.parser.smtlib.Absyn.IdentifierRef p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.CastIdentifierRef p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.SymbolRef p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* FunSignatureC */
    public R visit(ap.parser.smtlib.Absyn.FunSignature p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.FunSignatureC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* SortedVariableC */
    public R visit(ap.parser.smtlib.Absyn.SortedVariable p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.SortedVariableC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* ESortedVarC */
    public R visit(ap.parser.smtlib.Absyn.ESortedVar p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.ESortedVarC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* SpecConstant */
    public R visit(ap.parser.smtlib.Absyn.NumConstant p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.RatConstant p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.HexConstant p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.BinConstant p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.StringConstant p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.StringSQConstant p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.SpecConstant p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* MetaConstant */
    public R visit(ap.parser.smtlib.Absyn.NumMetaConstant p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.RatMetaConstant p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.HexMetaConstant p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.BinMetaConstant p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.StringMetaConstant p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.MetaConstant p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Identifier */
    public R visit(ap.parser.smtlib.Absyn.SymbolIdent p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.IndexIdent p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.Identifier p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* IndexC */
    public R visit(ap.parser.smtlib.Absyn.NumIndex p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.SymIndex p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.IndexC p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Symbol */
    public R visit(ap.parser.smtlib.Absyn.NormalSymbol p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.QuotedSymbol p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.Symbol p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* Annotation */
    public R visit(ap.parser.smtlib.Absyn.AttrAnnotation p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.Annotation p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* AttrParam */
    public R visit(ap.parser.smtlib.Absyn.SomeAttrParam p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.NoAttrParam p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.AttrParam p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
/* SExpr */
    public R visit(ap.parser.smtlib.Absyn.ConstantSExpr p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.SymbolSExpr p, A arg) { return visitDefault(p, arg); }
    public R visit(ap.parser.smtlib.Absyn.ParenSExpr p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(ap.parser.smtlib.Absyn.SExpr p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }

}
