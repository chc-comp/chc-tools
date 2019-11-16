### Model Validator
import sys
from .core import CliCmd, add_in_out_args
from .horndb import HornClauseDb, HornRule, FolModel, load_horn_db_from_file

import z3
import pysmt.solvers.z3 as pyz3

from pysmt.smtlib.parser import SmtLibZ3Parser, SmtLibCommand

def define_fun_to_lambda(env, cmd):
    converter = pyz3.Z3Converter(env, z3.get_ctx(None))
    name, params, ret_sort, body = cmd.args
    zparams = [converter.convert(p) for p in params]
    zbody = converter.convert(body)
    res = z3.Lambda(zparams, zbody)
    return res

def load_model_from_file(fname):
    print(fname)
    model = FolModel()
    with open(fname, 'r') as script:
        parser = SmtLibZ3Parser()
        for cmd in parser.get_command_generator(script):
            if type(cmd) == SmtLibCommand and cmd.name == 'define-fun':
                name = cmd.args[0]
                lmbd = define_fun_to_lambda(parser.env, cmd)
                model[name] = lmbd
                print(cmd)
    return model


class ModelValidator(object):
    def __init__(self, db, model):
        self._db = db
        self._model = model
        self._solver = z3.Solver()

    def _validate_rule(self, r):
        s = self._solver
        s.push()

        uninterp_sz = r.uninterp_size()
        for idx, term in enumerate(r.body()):
            if idx < uninterp_sz:
                s.add(self._model.eval(term))
            else:
                s.add(term)

        if not r.is_query():
            t = self._model.eval(r.head())
            s.add(z3.Not(t))

        res = s.check()
        if res == z3.unsat:
            pass
        else:
            print('Failed to validate a rule')
            print(r)
            if res == z3.sat:
                print('Model is')
                print(s.model())
            else:
                print('Incomplete solver')

        s.pop()
        return res == z3.unsat

    def validate(self):
        res = True
        for r in self._db.get_rules():
            v = self._validate_rule(r)
            res = res and v
        for q in self._db.get_queries():
            v = self._validate_rule(r)
            res = res and v
        return res

class ChcModelCmd(CliCmd):
    def __init__(self):
        super().__init__('chcmodel', 'Model validator', allow_extra=False)

    def mk_arg_parser(self, ap):
        ap = super().mk_arg_parser(ap)
        ap.add_argument('-m', dest='model_file',
                         metavar='FILE', help='Model in SMT2 format', default='model.smt2')
        ap.add_argument('in_file',  metavar='FILE', help='Input file')
        return ap

    def run(self, args, extra):
        db = load_horn_db_from_file(args.in_file)
        model = load_model_from_file(args.model_file)
        validator = ModelValidator(db, model)
        res = validator.validate()
        return 0 if res else 1;

if __name__ == '__main__':
    cmd = ChcModelCmd()
    sys.exit(cmd.main(sys.argv[1:]))
