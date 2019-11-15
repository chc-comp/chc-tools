### pretty printer
import sys
from .core import CliCmd, add_in_out_args

import z3

def load_fp_from_file(fname):
    fp = z3.Fixedpoint()
    q = fp.parse_file(fname)
    return (fp, q)

def pp_rules(fp, queries, out):
    fp.set('print_fixedpoint_extensions', True)
    print('(set-logic ALL)', file=out)
    out.write(fp.sexpr())
    for q in queries:
        out.write('(query {})\n'.format(q))

def pp_chc(fp, queries, out):
    fp.set('print_fixedpoint_extensions', False)
    #print('(set-logic HORN)', file=out)
    out.write(fp.sexpr())
    for q in queries:
        out.write('(assert {})\n'.format(z3.Implies(q, z3.BoolVal(False)).sexpr()))
    out.write('(check-sat)\n')

def pp_fp(fp, q, out, format='rules'):
    if format == 'rules':
        pp_rules(fp, q, out)
    else:
        pp_chc(fp, q, out)

class ChcPpCmd(CliCmd):
    def __init__(self):
        super().__init__('chcpp', 'Pretty-printer', allow_extra=False)

    def mk_arg_parser(self, ap):
        ap = super().mk_arg_parser(ap)
        ap.add_argument('-o', dest='out_file',
                         metavar='FILE', help='Output file name', default='out.smt2')
        ap.add_argument('in_file',  metavar='FILE', help='Input file')
        ap.add_argument('--format', help='Choice of format', default='rules',
                        choices=['rules', 'chc'])
        return ap

    def run(self, args, extra):
        fp, queries = load_fp_from_file(args.in_file)
        with open(args.out_file, 'w') as out:
            pp_fp(fp, queries, out, format=args.format)

        return 0

if __name__ == '__main__':
    cmd = ChcPpCmd()
    sys.exit(cmd.main(sys.argv[1:]))
