from abc import ABC, abstractmethod
from typing import MutableMapping, Optional, Callable, Any, List, TextIO, Union, Dict

import z3  # type: ignore


def z3_minus(z3_expr: z3.ExprRef) -> z3.ExprRef:
    if isinstance(z3_expr, z3.BoolRef):
        return z3.Not(z3_expr)
    elif isinstance(z3_expr, z3.BitVecRef):
        return ~z3_expr
    assert False


def to_z3_bitvec(z3_expr: z3.ExprRef) -> z3.BitVecRef:
    if isinstance(z3_expr, z3.BitVecRef):
        return z3_expr
    elif isinstance(z3_expr, z3.BoolRef):
        return z3.If(z3_expr, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
    assert False


def to_z3_bool(z3_expr: z3.ExprRef) -> z3.BoolRef:
    if isinstance(z3_expr, z3.BoolRef):
        return z3_expr
    elif isinstance(z3_expr, z3.BitVecRef):
        return z3_expr == z3.BitVecVal(1, 1)
    assert False


def to_z3_non_bool(z3_expr: z3.ExprRef) -> z3.ExprRef:
    if isinstance(z3_expr, z3.BoolRef):
        return z3.If(z3_expr, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
    else:
        return z3_expr


def to_z3_array(z3_expr: z3.ExprRef) -> z3.ArrayRef:
    if isinstance(z3_expr, z3.ArrayRef):
        return z3_expr
    assert False


# noinspection PyProtectedMember
def z3_bitvec_binary_op(z3_mk_bv: Callable[[Any, Any, Any], Any],
                        z3_bitvec1: z3.BitVecRef, z3_bitvec2: z3.BitVecRef) -> z3.BitVecRef:
    from z3.z3 import _coerce_exprs  # type: ignore
    a, b = _coerce_exprs(z3_bitvec1, z3_bitvec2)
    return z3.BitVecRef(z3_mk_bv(z3_bitvec1.ctx_ref(), a.as_ast(), b.as_ast()), z3_bitvec1.ctx)


class Node(ABC):
    symbol: str

    def __init__(self, symbol: str = ""):
        self.symbol = symbol


class Sort(Node):
    sid: int

    def __init__(self, sid: int, symbol: str = ""):
        super().__init__(symbol)
        self.sid = sid

    @abstractmethod
    def to_z3_sort(self) -> z3.SortRef:
        raise NotImplementedError

    @abstractmethod
    def booleanizable(self):
        raise NotImplementedError


class BitvecSort(Sort):
    width: int

    def __init__(self, sid: int, width: int, symbol: str = ""):
        super().__init__(sid, symbol)
        self.width = width

    def to_z3_sort(self) -> z3.SortRef:
        return z3.BitVecSort(self.width)

    def booleanizable(self) -> bool:
        return self.width == 1


class ArraySort(Sort):
    index_sort: Sort
    element_sort: Sort

    def __init__(self, sid: int, index_sort: Sort, element_sort: Sort, symbol: str = ""):
        super().__init__(sid, symbol)
        self.index_sort = index_sort
        self.element_sort = element_sort

    def to_z3_sort(self) -> z3.SortRef:
        return z3.ArraySort(self.index_sort.to_z3_sort(), self.element_sort.to_z3_sort())

    def booleanizable(self):
        return False


class Expr(Node):
    nid: int
    sort: Sort

    def __init__(self, nid: int, sort: Sort, symbol: str = ""):
        super().__init__(symbol)
        self.nid = nid
        self.sort = sort

    def to_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        if self.nid in m:
            return m[self.nid]
        else:
            z3_expr: z3.ExprRef = self.__to_fresh_z3_expr(m)
            m[self.nid] = z3_expr
            return z3_expr

    def booleanizable(self):
        return self.sort.booleanizable()

    def get_z3_sort(self) -> z3.SortRef:
        return self.sort.to_z3_sort()

    @abstractmethod
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        raise NotImplementedError


class Bitvec(Expr, ABC):
    sort: BitvecSort

    def __init__(self, nid: int, sort: BitvecSort, symbol: str = ""):
        super().__init__(nid, sort, symbol)

    def width(self) -> int:
        return self.sort.width

    def to_z3_bitvec(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return to_z3_bitvec(self.to_z3_expr(m))

    def to_z3_bool(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return to_z3_bool(self.to_z3_expr(m))


class Array(Expr, ABC):
    sort: ArraySort

    def __init__(self, nid: int, sort: ArraySort, symbol: str = ""):
        super().__init__(nid, sort, symbol)

    def to_z3_array(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ArrayRef:
        return to_z3_array(self.to_z3_expr(m))


class Minus(Bitvec):
    bitvec: Bitvec

    def __init__(self, bitvec: Bitvec):
        super().__init__(bitvec.nid, bitvec.sort)
        self.bitvec = bitvec

    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        return z3_minus(self.bitvec.to_z3_expr(m))


class BitvecInput(Bitvec):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        prefix = self.symbol if self.symbol else "input_{:d}".format(self.nid)
        sort = z3.BoolSort() if self.booleanizable() else self.get_z3_sort()
        return z3.FreshConst(sort, prefix=prefix)


class ArrayInput(Array):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        prefix = self.symbol if self.symbol else "input_{:d}".format(self.nid)
        sort = z3.BoolSort() if self.booleanizable() else self.get_z3_sort()
        return z3.FreshConst(sort, prefix=prefix)


class Constant(Bitvec):
    value: int

    def __init__(self, nid: int, sort: BitvecSort, value: int, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.value = value

    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        return z3.BoolVal(self.value) if self.booleanizable() else z3.BitVecVal(self.value, self.width())


class One(Constant):
    def __init__(self, nid: int, sort: BitvecSort, symbol: str = ""):
        super().__init__(nid, sort, 1, symbol)


class Ones(Constant):
    def __init__(self, nid: int, sort: BitvecSort, symbol: str = ""):
        super().__init__(nid, sort, -1, symbol)


class Zero(Constant):
    def __init__(self, nid: int, sort: BitvecSort, symbol: str = ""):
        super().__init__(nid, sort, 0, symbol)


class Const(Constant):
    def __init__(self, nid: int, sort: BitvecSort, bin_str: str, symbol: str = ""):
        super().__init__(nid, sort, int(bin_str, 2), symbol)


class Constd(Constant):
    def __init__(self, nid: int, sort: BitvecSort, dec_str: str, symbol: str = ""):
        super().__init__(nid, sort, int(dec_str, 10), symbol)


class Consth(Constant):
    def __init__(self, nid: int, sort: BitvecSort, hex_str: str, symbol: str = ""):
        super().__init__(nid, sort, int(hex_str, 16), symbol)


# noinspection DuplicatedCode
class BitvecState(Bitvec):
    __init_bitvec: Optional[Bitvec]
    __next_bitvec: Optional[Bitvec]

    def __init__(self, nid: int, sort: BitvecSort, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.__init_bitvec = None
        self.__next_bitvec = None

    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        prefix = self.symbol if self.symbol else "state_{:d}".format(self.nid)
        sort = z3.BoolSort() if self.booleanizable() else self.get_z3_sort()
        return z3.FreshConst(sort, prefix=prefix)

    @property
    def init_bitvec(self) -> Optional[Bitvec]:
        return self.__init_bitvec

    @init_bitvec.setter
    def init_bitvec(self, init_bitvec: Bitvec) -> None:
        if self.__init_bitvec is not None:
            raise ValueError
        self.__init_bitvec = init_bitvec

    @property
    def next_bitvec(self) -> Optional[Bitvec]:
        return self.__next_bitvec

    @next_bitvec.setter
    def next_bitvec(self, next_bitvec: Bitvec) -> None:
        if self.__next_bitvec is not None:
            raise ValueError
        self.__next_bitvec = next_bitvec


# noinspection DuplicatedCode
class ArrayState(Array):
    __init_bitvec: Optional[Array]
    __next_bitvec: Optional[Array]

    def __init__(self, nid: int, sort: ArraySort, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.__init_bitvec = None
        self.__next_bitvec = None

    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ArrayRef:
        prefix = self.symbol if self.symbol else "state_{:d}".format(self.nid)
        sort = z3.BoolSort() if self.booleanizable() else self.get_z3_sort()
        return z3.FreshConst(sort, prefix=prefix)

    @property
    def init_array(self) -> Optional[Array]:
        return self.__init_bitvec

    @init_array.setter
    def init_array(self, init_bitvec: Array) -> None:
        if self.__init_bitvec is not None:
            raise ValueError
        self.__init_bitvec = init_bitvec

    @property
    def next_array(self) -> Optional[Array]:
        return self.__next_bitvec

    @next_array.setter
    def next_array(self, next_bitvec: Array) -> None:
        if self.__next_bitvec is not None:
            raise ValueError
        self.__next_bitvec = next_bitvec


class Ext(Bitvec, ABC):
    bitvec: Bitvec
    w: int

    def __init__(self, nid: int, sort: BitvecSort, bitvec: Bitvec, w: int, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.bitvec = bitvec
        self.w = w

    def get_child_z3_bitvec(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.bitvec.to_z3_bitvec(m)


class Sext(Ext):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return z3.SignExt(self.w, self.get_child_z3_bitvec(m))


class Uext(Ext):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return z3.ZeroExt(self.w, self.get_child_z3_bitvec(m))


class Slice(Bitvec):
    bitvec: Bitvec
    upper: int
    lower: int

    def __init__(self, nid: int, sort: BitvecSort, bitvec: Bitvec, upper: int, lower: int, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.bitvec = bitvec
        self.upper = upper
        self.lower = lower

    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return z3.Extract(self.upper, self.lower, self.bitvec.to_z3_bitvec(m))


class BitvecUnaryOp(Bitvec, ABC):
    bitvec: Bitvec

    def __init__(self, nid: int, sort: BitvecSort, bitvec: Bitvec, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.bitvec = bitvec

    def get_child_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        return self.bitvec.to_z3_expr(m)

    def get_child_z3_bitvec(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.bitvec.to_z3_bitvec(m)

    def get_child_z3_bool(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return self.bitvec.to_z3_bool(m)


class Not(BitvecUnaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        return z3_minus(self.bitvec.to_z3_expr(m))


class Inc(BitvecUnaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.get_child_z3_bitvec(m) + 1


class Dec(BitvecUnaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.get_child_z3_bitvec(m) + 1


class Neg(BitvecUnaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return -self.get_child_z3_bitvec(m)


class Redand(BitvecUnaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.BVRedAnd(self.get_child_z3_bitvec(m))


class Redor(BitvecUnaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.BVRedOr(self.get_child_z3_bitvec(m))


class Redxor(BitvecUnaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        # TODO
        pass


class BitvecBinaryOp(Bitvec, ABC):
    bitvec1: Bitvec
    bitvec2: Bitvec

    def __init__(self, nid: int, sort: BitvecSort, bitvec1: Bitvec, bitvec2: Bitvec, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.bitvec1 = bitvec1
        self.bitvec2 = bitvec2

    def get_child1_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        return self.bitvec1.to_z3_expr(m)

    def get_child2_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        return self.bitvec2.to_z3_expr(m)

    def get_child1_z3_bitvec(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.bitvec1.to_z3_bitvec(m)

    def get_child2_z3_bitvec(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.bitvec2.to_z3_bitvec(m)

    def get_child1_z3_bool(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return self.bitvec1.to_z3_bool(m)

    def get_child2_z3_bool(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return self.bitvec2.to_z3_bool(m)


class Iff(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return self.get_child1_z3_bool(m) == self.get_child2_z3_bool(m)


class Implies(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.Implies(self.get_child1_z3_bool(m), self.get_child2_z3_bool(m))


class Equality(Bitvec, ABC):
    expr1: Expr
    expr2: Expr

    def __init__(self, nid: int, sort: BitvecSort, expr1: Expr, expr2, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.expr1 = expr1
        self.expr2 = expr2

    def get_child1_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        return self.expr1.to_z3_expr(m)

    def get_child2_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        return self.expr2.to_z3_expr(m)


class Eq(Equality):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        z3_expr1: z3.ExprRef = self.get_child1_z3_expr(m)
        z3_expr2: z3.ExprRef = self.get_child2_z3_expr(m)
        if isinstance(z3_expr1, z3.BoolRef) or isinstance(z3_expr2, z3.BoolRef):
            return to_z3_bool(z3_expr1) == to_z3_bool(z3_expr2)
        else:
            return z3_expr1 == z3_expr2


class Neq(Equality):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        z3_expr1: z3.ExprRef = self.get_child1_z3_expr(m)
        z3_expr2: z3.ExprRef = self.get_child2_z3_expr(m)
        if isinstance(z3_expr1, z3.BoolRef) or isinstance(z3_expr2, z3.BoolRef):
            return to_z3_bool(z3_expr1) != to_z3_bool(z3_expr2)
        else:
            return z3_expr1 != z3_expr2


class Sgt(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return self.get_child1_z3_bitvec(m) > self.get_child2_z3_bitvec(m)


class Ugt(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.UGT(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class Sgte(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return self.get_child1_z3_bitvec(m) >= self.get_child2_z3_bitvec(m)


class Ugte(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.UGE(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class Slt(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return self.get_child1_z3_bitvec(m) < self.get_child2_z3_bitvec(m)


class Ult(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.ULT(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class Slte(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return self.get_child1_z3_bitvec(m) <= self.get_child2_z3_bitvec(m)


class Ulte(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.ULE(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class And(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        z3_expr1: z3.ExprRef = self.to_z3_expr(m)
        z3_expr2: z3.ExprRef = self.to_z3_expr(m)
        if isinstance(z3_expr1, z3.BoolRef) or isinstance(z3_expr2, z3.BoolRef):
            return z3.And(to_z3_bool(z3_expr1), to_z3_bool(z3_expr2))
        else:
            assert isinstance(z3_expr1, z3.BitVecRef) and isinstance(z3_expr2, z3.BitVecRef)
            return z3_expr1 & z3_expr2


class Nand(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        z3_expr1: z3.ExprRef = self.to_z3_expr(m)
        z3_expr2: z3.ExprRef = self.to_z3_expr(m)
        if isinstance(z3_expr1, z3.BoolRef) or isinstance(z3_expr2, z3.BoolRef):
            return z3.Not(z3.And(to_z3_bool(z3_expr1), to_z3_bool(z3_expr2)))
        else:
            assert isinstance(z3_expr1, z3.BitVecRef) and isinstance(z3_expr2, z3.BitVecRef)
            return z3_bitvec_binary_op(z3.Z3_mk_bvnand, z3_expr1, z3_expr2)


class Nor(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        z3_expr1: z3.ExprRef = self.to_z3_expr(m)
        z3_expr2: z3.ExprRef = self.to_z3_expr(m)
        if isinstance(z3_expr1, z3.BoolRef) or isinstance(z3_expr2, z3.BoolRef):
            return z3.Not(z3.Or(to_z3_bool(z3_expr1), to_z3_bool(z3_expr2)))
        else:
            assert isinstance(z3_expr1, z3.BitVecRef) and isinstance(z3_expr2, z3.BitVecRef)
            return z3_bitvec_binary_op(z3.Z3_mk_bvnor, z3_expr1, z3_expr2)


class Or(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        z3_expr1: z3.ExprRef = self.to_z3_expr(m)
        z3_expr2: z3.ExprRef = self.to_z3_expr(m)
        if isinstance(z3_expr1, z3.BoolRef) or isinstance(z3_expr2, z3.BoolRef):
            return z3.Or(to_z3_bool(z3_expr1), to_z3_bool(z3_expr2))
        else:
            assert isinstance(z3_expr1, z3.BitVecRef) and isinstance(z3_expr2, z3.BitVecRef)
            return z3_expr1 | z3_expr2


class Xnor(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        z3_expr1: z3.ExprRef = self.to_z3_expr(m)
        z3_expr2: z3.ExprRef = self.to_z3_expr(m)
        if isinstance(z3_expr1, z3.BoolRef) or isinstance(z3_expr2, z3.BoolRef):
            return z3.Not(z3.Xor(to_z3_bool(z3_expr1), to_z3_bool(z3_expr2)))
        else:
            assert isinstance(z3_expr1, z3.BitVecRef) and isinstance(z3_expr2, z3.BitVecRef)
            return z3_bitvec_binary_op(z3.Z3_mk_bvxnor, z3_expr1, z3_expr2)


class Xor(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        z3_expr1: z3.ExprRef = self.to_z3_expr(m)
        z3_expr2: z3.ExprRef = self.to_z3_expr(m)
        if isinstance(z3_expr1, z3.BoolRef) or isinstance(z3_expr2, z3.BoolRef):
            return z3.Xor(to_z3_bool(z3_expr1), to_z3_bool(z3_expr2))
        else:
            assert isinstance(z3_expr1, z3.BitVecRef) and isinstance(z3_expr2, z3.BitVecRef)
            return z3_expr1 ^ z3_expr2


class Sll(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.get_child1_z3_bitvec(m) << self.get_child2_z3_bitvec(m)


class Sra(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.get_child1_z3_bitvec(m) >> self.get_child2_z3_bitvec(m)


class Srl(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return z3.LShR(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class Rol(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return z3.RotateLeft(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class Ror(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return z3.RotateRight(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class Add(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.get_child1_z3_bitvec(m) + self.get_child2_z3_bitvec(m)


class Mul(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.get_child1_z3_bitvec(m) * self.get_child2_z3_bitvec(m)


class Sdiv(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.get_child1_z3_bitvec(m) / self.get_child2_z3_bitvec(m)


class Udiv(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return z3.UDiv(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class Smod(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.get_child1_z3_bitvec(m) % self.get_child2_z3_bitvec(m)


class Srem(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return z3.SRem(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class Urem(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return z3.URem(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class Sub(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return self.get_child1_z3_bitvec(m) - self.get_child2_z3_bitvec(m)


class Saddo(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.Not(z3.Or((z3.BVAddNoOverflow(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m), True),
                             z3.BVAddNoUnderflow(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m)))))


class Uaddo(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.Not(z3.BVAddNoOverflow(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m), False))


class Sdivo(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.Not(z3.BVSDivNoOverflow(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m)))


class Udivo(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.BoolVal(False)


class Smulo(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.Not(z3.Or((z3.BVMulNoOverflow(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m), True),
                             z3.BVMulNoUnderflow(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m)))))


class Umulo(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.Not(z3.BVMulNoOverflow(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m), False))


class Ssubo(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.Not(z3.Or((z3.BVSubNoUnderflow(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m), True),
                             z3.BVSubNoOverflow(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m)))))


class Usubo(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BoolRef:
        return z3.Not(z3.BVSubNoUnderflow(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m), False))


class Concat(BitvecBinaryOp):
    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.BitVecRef:
        return z3.Concat(self.get_child1_z3_bitvec(m), self.get_child2_z3_bitvec(m))


class BitvecRead(Bitvec):
    array: Array
    expr: Expr

    def __init__(self, nid: int, sort: BitvecSort, array: Array, expr: Expr, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.array = array
        self.expr = expr

    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        return self.array.to_z3_array(m)[to_z3_non_bool(self.expr.to_z3_expr(m))]


class ArrayRead(Array):
    array: Array
    expr: Expr

    def __init__(self, nid: int, sort: ArraySort, array: Array, expr: Expr, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.array = array
        self.expr = expr

    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        return self.array.to_z3_array(m)[to_z3_non_bool(self.expr.to_z3_expr(m))]


class Ite(Bitvec):
    bitvec1: Bitvec
    bitvec2: Bitvec
    bitvec3: Bitvec

    def __init__(self, nid: int, sort: BitvecSort, bitvec1: Bitvec, bitvec2: Bitvec, bitvec3: Bitvec, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.bitvec1 = bitvec1
        self.bitvec2 = bitvec2
        self.bitvec3 = bitvec3

    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ExprRef:
        z3_expr2: z3.ExprRef = self.bitvec2.to_z3_expr(m)
        z3_expr3: z3.ExprRef = self.bitvec3.to_z3_expr(m)
        if isinstance(z3_expr2, z3.BoolRef) or isinstance(z3_expr3, z3.BoolRef):
            return z3.If(self.bitvec1.to_z3_bool(m), to_z3_bool(z3_expr2), to_z3_bool(z3_expr3))
        else:
            return z3.If(self.bitvec1.to_z3_bool(m), z3_expr2, z3_expr3)


class Write(Array):
    array: Array
    expr1: Expr
    expr2: Expr

    def __init__(self, nid: int, sort: ArraySort, array: Array, expr1: Expr, expr2: Expr, symbol: str = ""):
        super().__init__(nid, sort, symbol)
        self.array = array
        self.expr1 = expr1
        self.expr2 = expr2

    def __to_fresh_z3_expr(self, m: MutableMapping[int, z3.ExprRef]) -> z3.ArrayRef:
        return z3.Update(self.array.to_z3_array(m),
                         to_z3_non_bool(self.expr1.to_z3_expr(m)),
                         to_z3_non_bool(self.expr2.to_z3_expr(m)))


class BitvecInit(Node):
    nid: int
    sort: BitvecSort
    state: BitvecState
    bitvec: Bitvec

    def __init__(self, nid: int, sort: BitvecSort, state: BitvecState, bitvec: Bitvec, symbol: str = ""):
        super().__init__(symbol)
        self.nid = nid
        self.sort = sort
        self.state = state
        self.bitvec = bitvec


class ArrayInit(Node):
    nid: int
    sort: ArraySort
    state: ArrayState
    array: Array

    def __init__(self, nid: int, sort: ArraySort, state: ArrayState, bitvec: Bitvec, symbol: str = ""):
        super().__init__(symbol)
        self.nid = nid
        self.sort = sort
        self.state = state
        self.bitvec = bitvec


class BitvecNext(Node):
    nid: int
    sort: BitvecSort
    state: BitvecState
    bitvec: Bitvec

    def __init__(self, nid: int, sort: BitvecSort, state: BitvecState, bitvec: Bitvec, symbol: str = ""):
        super().__init__(symbol)
        self.nid = nid
        self.sort = sort
        self.state = state
        self.bitvec = bitvec


class ArrayNext(Node):
    nid: int
    sort: ArraySort
    state: ArrayState
    array: Array

    def __init__(self, nid: int, sort: ArraySort, state: ArrayState, bitvec: Bitvec, symbol: str = ""):
        super().__init__(symbol)
        self.nid = nid
        self.sort = sort
        self.state = state
        self.bitvec = bitvec


class Bad(Node):
    nid: int
    bitvec: Bitvec

    def __init__(self, nid: int, bitvec: Bitvec, symbol: str = ""):
        super().__init__(symbol)
        self.nid = nid
        self.bitvec = bitvec


class Constraint(Node):
    nid: int
    bitvec: Bitvec

    def __init__(self, nid: int, bitvec: Bitvec, symbol: str = ""):
        super().__init__(symbol)
        self.nid = nid
        self.bitvec = bitvec


class Fair(Node):
    nid: int
    expr: Expr

    def __init__(self, nid: int, expr: Expr, symbol: str = ""):
        super().__init__(symbol)
        self.nid = nid
        self.expr = expr


class Output(Node):
    nid: int
    expr: Expr

    def __init__(self, nid: int, expr: Expr, symbol: str = ""):
        super().__init__(symbol)
        self.nid = nid
        self.expr = expr


class Justice(Node):
    nid: int
    n: int
    expr_list: List[Expr]

    def __init__(self, nid: int, n: int, expr_list: List[Expr], symbol: str = ""):
        super().__init__(symbol)
        self.nid = nid
        self.n = n
        self.expr_list = expr_list


class Btor2Parser:
    bitvec_sort_table: Dict[int, BitvecSort]
    array_sort_table: Dict[int, ArraySort]
    bitvec_state_table: Dict[int, BitvecState]
    array_state_table: Dict[int, ArrayState]
    bitvec_table: Dict[int, Bitvec]
    array_table: Dict[int, Array]
    bad_list: List[Bad]
    constraint_list: List[Constraint]
    fair_list: List[Fair]
    output_list: List[Output]
    justice_list: List[Justice]

    def __init__(self):
        self.bitvec_sort_table = {}
        self.array_sort_table = {}
        self.bitvec_state_table = {}
        self.array_state_table = {}
        self.bitvec_table = {}
        self.array_table = {}
        self.bad_list = []
        self.constraint_list = []
        self.fair_list = []
        self.output_list = []
        self.justice_list = []

    def get_sort(self, s: Union[int, str]) -> Sort:
        sid: int = int(s)
        return self.bitvec_sort_table[sid] if sid in self.bitvec_sort_table else self.array_sort_table[sid]

    def get_bitvec_sort(self, s: Union[int, str]) -> BitvecSort:
        return self.bitvec_sort_table[int(s)]

    def get_array_sort(self, s: Union[int, str]) -> ArraySort:
        return self.array_sort_table[int(s)]

    def get_expr(self, n: Union[int, str]) -> Expr:
        nid: int = int(n)
        return self.bitvec_table[nid] if nid in self.bitvec_table else self.array_table[nid]

    def get_bitvec_state(self, n: Union[int, str]) -> BitvecState:
        return self.bitvec_state_table[int(n)]

    def get_array_state(self, n: Union[int, str]) -> ArrayState:
        return self.array_state_table[int(n)]

    def get_bitvec(self, n: Union[int, str]) -> Bitvec:
        return self.bitvec_table[int(n)]

    def get_array(self, n: Union[int, str]) -> Array:
        return self.array_table[int(n)]

    def parse(self, source: TextIO):
        for line in source:
            line_left: str
            sep: str
            line_right: str
            line_left, sep, line_right = line.partition(';')
            tokens: List[str] = line_left.split()

            if len(tokens) == 0:
                continue

            name: str = tokens[1]
            if name == 'sort':
                sid: int = int(tokens[0])
                if tokens[2] == 'array':
                    self.array_sort_table[sid] = ArraySort(sid, self.get_sort(tokens[3]), self.get_sort(tokens[4]))
                elif tokens[2] == 'bitvec':
                    self.bitvec_sort_table[sid] = BitvecSort(sid, int(tokens[3]))
                continue

            nid: int = int(tokens[0])

            if name == 'bad':
                self.bad_list.append(Bad(nid, self.get_bitvec(tokens[2])))
                continue
            elif name == 'constraint':
                self.constraint_list.append(Constraint(nid, self.get_bitvec(tokens[2])))
                continue
            elif name == 'fair':
                self.fair_list.append(Fair(nid, self.get_expr(tokens[2])))
                continue
            elif name == 'output':
                self.output_list.append(Output(nid, self.get_expr(tokens[2])))
                continue
            elif name == 'justice':
                n: int = int(tokens[2])
                self.justice_list.append(Justice(nid, n, [self.get_expr(x) for x in tokens[3:3 + n]]))
                continue

            # noinspection DuplicatedCode
            if name == 'read':
                read_sid: int = int(tokens[2])
                if read_sid in self.bitvec_sort_table:
                    self.bitvec_table[nid] = BitvecRead(nid, self.get_bitvec_sort(read_sid), self.get_array(tokens[3]),
                                                        self.get_expr(tokens[4]))
                elif read_sid in self.array_sort_table:
                    self.array_table[nid] = ArrayRead(nid, self.get_array_sort(read_sid), self.get_array(tokens[3]),
                                                      self.get_expr(tokens[4]))
                continue
            elif name == 'state':
                state_sid: int = int(tokens[2])
                if state_sid in self.bitvec_sort_table:
                    bitvec_state: BitvecState = BitvecState(nid, self.get_bitvec_sort(state_sid))
                    self.bitvec_state_table[nid] = self.bitvec_table[nid] = bitvec_state
                elif state_sid in self.array_sort_table:
                    array_state: ArrayState = ArrayState(nid, self.get_array_sort(state_sid))
                    self.array_state_table[nid] = self.array_table[nid] = array_state
                continue
            elif name == 'input':
                input_sid: int = int(tokens[2])
                if input_sid in self.bitvec_sort_table:
                    self.bitvec_table[nid] = BitvecInput(nid, self.get_bitvec_sort(input_sid))
                elif input_sid in self.array_sort_table:
                    self.array_table[nid] = ArrayInput(nid, self.get_array_sort(input_sid))
                continue
            elif name == 'init':
                init_sid: int = int(tokens[2])
                if init_sid in self.bitvec_sort_table:
                    self.get_bitvec_state(tokens[3]).init_bitvec = self.get_bitvec(tokens[4])
                elif init_sid in self.array_sort_table:
                    self.get_array_state(tokens[3]).init_array = self.get_array(tokens[4])
                continue
            elif name == 'next':
                next_sid: int = int(tokens[2])
                if next_sid in self.bitvec_sort_table:
                    self.get_bitvec_state(tokens[3]).next_bitvec = self.get_bitvec(tokens[4])
                elif next_sid in self.array_sort_table:
                    self.get_array_state(tokens[3]).next_array = self.get_array(tokens[4])
                continue
            elif name == 'write':
                self.array_table[nid] = Write(nid, self.get_array_sort(int(tokens[2])), self.get_array(tokens[3]),
                                              self.get_expr(tokens[4]), self.get_expr(tokens[5]))
                continue

            sort: BitvecSort = self.get_bitvec_sort(tokens[2])
            if name == 'one':
                self.bitvec_table[nid] = One(nid, sort)
            elif name == 'ones':
                self.bitvec_table[nid] = Ones(nid, sort)
            elif name == 'zero':
                self.bitvec_table[nid] = Zero(nid, sort)
            elif name == 'const':
                self.bitvec_table[nid] = Const(nid, sort, tokens[3])
            elif name == 'constd':
                self.bitvec_table[nid] = Constd(nid, sort, tokens[3])
            elif name == 'consth':
                self.bitvec_table[nid] = Consth(nid, sort, tokens[3])
            elif name == 'sext':
                self.bitvec_table[nid] = Sext(nid, sort, self.get_bitvec(tokens[3]), int(tokens[4]))
            elif name == 'slice':
                self.bitvec_table[nid] = Slice(nid, sort, self.get_bitvec(tokens[3]), int(tokens[4]), int(tokens[5]))
            elif name == 'not':
                self.bitvec_table[nid] = Not(nid, sort, self.get_bitvec(tokens[3]))
            elif name == 'inc':
                self.bitvec_table[nid] = Inc(nid, sort, self.get_bitvec(tokens[3]))
            elif name == 'dec':
                self.bitvec_table[nid] = Dec(nid, sort, self.get_bitvec(tokens[3]))
            elif name == 'neg':
                self.bitvec_table[nid] = Neg(nid, sort, self.get_bitvec(tokens[3]))
            elif name == 'redand':
                self.bitvec_table[nid] = Redand(nid, sort, self.get_bitvec(tokens[3]))
            elif name == 'redor':
                self.bitvec_table[nid] = Redor(nid, sort, self.get_bitvec(tokens[3]))
            elif name == 'redxor':
                self.bitvec_table[nid] = Redxor(nid, sort, self.get_bitvec(tokens[3]))
            elif name == 'iff':
                self.bitvec_table[nid] = Iff(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'implies':
                self.bitvec_table[nid] = Implies(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'eq':
                self.bitvec_table[nid] = Eq(nid, sort, self.get_expr(tokens[3]), self.get_expr(tokens[4]))
            elif name == 'neq':
                self.bitvec_table[nid] = Neq(nid, sort, self.get_expr(tokens[3]), self.get_expr(tokens[4]))
            elif name == 'sgt':
                self.bitvec_table[nid] = Sgt(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'ugt':
                self.bitvec_table[nid] = Ugt(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'sgte':
                self.bitvec_table[nid] = Sgte(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'ugte':
                self.bitvec_table[nid] = Ugte(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'slt':
                self.bitvec_table[nid] = Slt(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'ult':
                self.bitvec_table[nid] = Ult(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'slte':
                self.bitvec_table[nid] = Slte(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'ulte':
                self.bitvec_table[nid] = Ulte(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'and':
                self.bitvec_table[nid] = And(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'nand':
                self.bitvec_table[nid] = Nand(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'nor':
                self.bitvec_table[nid] = Nor(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'or':
                self.bitvec_table[nid] = Or(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'xnor':
                self.bitvec_table[nid] = Xnor(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'xor':
                self.bitvec_table[nid] = Xor(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'rol':
                self.bitvec_table[nid] = Rol(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'ror':
                self.bitvec_table[nid] = Ror(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'sll':
                self.bitvec_table[nid] = Sll(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'sra':
                self.bitvec_table[nid] = Sra(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'srl':
                self.bitvec_table[nid] = Srl(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'add':
                self.bitvec_table[nid] = Add(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'mul':
                self.bitvec_table[nid] = Mul(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'sdiv':
                self.bitvec_table[nid] = Sdiv(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'udiv':
                self.bitvec_table[nid] = Udiv(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'smod':
                self.bitvec_table[nid] = Smod(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'srem':
                self.bitvec_table[nid] = Srem(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'urem':
                self.bitvec_table[nid] = Urem(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'sub':
                self.bitvec_table[nid] = Sub(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'saddo':
                self.bitvec_table[nid] = Saddo(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'uaddo':
                self.bitvec_table[nid] = Uaddo(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'sdivo':
                self.bitvec_table[nid] = Sdivo(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'udivo':
                self.bitvec_table[nid] = Udivo(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'smulo':
                self.bitvec_table[nid] = Smulo(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'umulo':
                self.bitvec_table[nid] = Umulo(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'ssubo':
                self.bitvec_table[nid] = Ssubo(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'usubo':
                self.bitvec_table[nid] = Usubo(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'concat':
                self.bitvec_table[nid] = Concat(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]))
            elif name == 'ite':
                self.bitvec_table[nid] = Ite(nid, sort, self.get_bitvec(tokens[3]), self.get_bitvec(tokens[4]),
                                             self.get_bitvec(tokens[5]))
