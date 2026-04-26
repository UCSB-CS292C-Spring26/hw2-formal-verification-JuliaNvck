"""
CS292C Homework 2 — Problem 2: Hoare Logic VCG for IMP (30 points)
===================================================================
Implement weakest-precondition-based verification condition generation
for a simple IMP language, using Z3 to discharge the VCs.

Part (a): Compute wp using your VCG and analyze preconditions with Z3.
          NOTE: Part (a) depends on Part (b). Implement Part (b) first, then come back to Part (a).
Part (b): Implement wp() and verify() below.
Part (c): Discover loop invariants for three programs.
Part (d): Find and fix a bug in a provided invariant.
"""

from z3 import *
from dataclasses import dataclass
from typing import Union

# ============================================================================
# IMP Abstract Syntax Tree
# ============================================================================

@dataclass
class IntConst:
    value: int

@dataclass
class Var:
    name: str

@dataclass
class BinOp:
    """op ∈ {'+', '-', '*'}"""
    op: str
    left: 'AExp'
    right: 'AExp'

AExp = Union[IntConst, Var, BinOp]

@dataclass
class BoolConst:
    value: bool

@dataclass
class Compare:
    """op ∈ {'<', '<=', '>', '>=', '==', '!='}"""
    op: str
    left: AExp
    right: AExp

@dataclass
class ImpNot:
    expr: 'BExp'

@dataclass
class ImpAnd:
    left: 'BExp'
    right: 'BExp'

@dataclass
class ImpOr:
    left: 'BExp'
    right: 'BExp'

BExp = Union[BoolConst, Compare, ImpNot, ImpAnd, ImpOr]

@dataclass
class Assign:
    var: str
    expr: AExp

@dataclass
class Seq:
    s1: 'Stmt'
    s2: 'Stmt'

@dataclass
class If:
    cond: BExp
    then_branch: 'Stmt'
    else_branch: 'Stmt'

@dataclass
class While:
    cond: BExp
    invariant: 'BExp'
    body: 'Stmt'

@dataclass
class Assert:
    cond: BExp

@dataclass
class Assume:
    cond: BExp

Stmt = Union[Assign, Seq, If, While, Assert, Assume]

# ============================================================================
# IMP AST → Z3 Translation
# ============================================================================

_z3_vars: dict[str, ArithRef] = {}

def z3_var(name: str) -> ArithRef:
    if name not in _z3_vars:
        _z3_vars[name] = Int(name)
    return _z3_vars[name]

def aexp_to_z3(e: AExp) -> ArithRef:
    match e:
        case IntConst(v):   return IntVal(v)
        case Var(name):     return z3_var(name)
        case BinOp('+', l, r): return aexp_to_z3(l) + aexp_to_z3(r)
        case BinOp('-', l, r): return aexp_to_z3(l) - aexp_to_z3(r)
        case BinOp('*', l, r): return aexp_to_z3(l) * aexp_to_z3(r)
        case _: raise ValueError(f"Unknown AExp: {e}")

def bexp_to_z3(e: BExp) -> BoolRef:
    match e:
        case BoolConst(v):   return BoolVal(v)
        case Compare(op, l, r):
            lz, rz = aexp_to_z3(l), aexp_to_z3(r)
            return {'<': lz < rz, '<=': lz <= rz, '>': lz > rz,
                    '>=': lz >= rz, '==': lz == rz, '!=': lz != rz}[op]
        case ImpNot(inner):  return z3.Not(bexp_to_z3(inner))
        case ImpAnd(l, r):   return z3.And(bexp_to_z3(l), bexp_to_z3(r))
        case ImpOr(l, r):    return z3.Or(bexp_to_z3(l), bexp_to_z3(r))
        case _: raise ValueError(f"Unknown BExp: {e}")

def z3_substitute_var(formula: ExprRef, var_name: str, replacement: ArithRef) -> ExprRef:
    """Replace every occurrence of z3 variable `var_name` with `replacement`."""
    return substitute(formula, (z3_var(var_name), replacement))


# ============================================================================
# Part (b): Weakest Precondition + VCG — 12 pts
# ============================================================================

side_vcs: list[tuple[str, BoolRef]] = []

def wp(stmt: Stmt, Q: BoolRef) -> BoolRef:
    """
    Compute the weakest precondition of `stmt` w.r.t. postcondition `Q`.
    For while loops, append side VCs to the global `side_vcs` list.
    """
    global side_vcs

    match stmt:
        case Assign(var, expr):
            # Q[var ↦ expr]
            Q = z3_substitute_var(Q, var, aexp_to_z3(expr))
            return Q

        case Seq(s1, s2):
            return wp(s1, wp(s2, Q))

        case If(cond, s1, s2):
            return z3.And(
                z3.Implies(bexp_to_z3(cond), wp(s1, Q)),
                z3.Implies(z3.Not(bexp_to_z3(cond)), wp(s2, Q))
            )

        case While(cond, inv, body):
            # Return I. Generate two side VCs:
            #   preservation: I ∧ b → wp(body, I)
            #   postcondition: I ∧ ¬b → Q
            preservation_vc = z3.Implies(z3.And(bexp_to_z3(inv), bexp_to_z3(cond)),
                                        wp(body, bexp_to_z3(inv)))
            postcondition_vc = z3.Implies(z3.And(bexp_to_z3(inv), z3.Not(bexp_to_z3(cond))), Q)
            side_vcs.append(("Loop Preservation", preservation_vc))
            side_vcs.append(("Loop Postcondition", postcondition_vc))
            return bexp_to_z3(inv)

        case Assert(cond):
            return z3.And(bexp_to_z3(cond), Q)

        case Assume(cond):
            return z3.Implies(bexp_to_z3(cond), Q)

        case _:
            raise ValueError(f"Unknown statement: {stmt}")


def verify(pre: BExp, stmt: Stmt, post: BExp, label: str = "Program"):
    """
    Verify the Hoare triple {pre} stmt {post}.
    1. Clear side_vcs.  2. Compute wp.  3. Check pre → wp is valid.
    4. Check each side VC.  5. Print results.
    """
    global side_vcs
    side_vcs = []

    pre_z3 = bexp_to_z3(pre)
    post_z3 = bexp_to_z3(post)

    wp_z3 = wp(stmt, post_z3)
    s = Solver()
    s.add(Not(Implies(pre_z3, wp_z3)))
    result = s.check()
    valid = (result == unsat)

    print(f"=== {label} ===")
    print("  Precondition:", pre_z3, "→" if valid else "⊬", "wp is valid")
    if not valid:
        print("    Counterexample:", s.model())
    for vc_label, vc in side_vcs:
        s = Solver()
        s.add(Not(vc))
        result = s.check()
        valid = (result == unsat)
        print(f"  Side VC ({vc_label}):", vc, "is", "VALID" if valid else "INVALID")
        if not valid:
            print("    Counterexample:", s.model())
    print()


# ============================================================================
# Test Programs for Part (b) — verify your VCG works on these
# ============================================================================

def test_swap():
    """{ x == a ∧ y == b }  t:=x; x:=y; y:=t  { x == b ∧ y == a }"""
    pre = ImpAnd(Compare('==', Var('x'), Var('a')),
                 Compare('==', Var('y'), Var('b')))
    stmt = Seq(Assign('t', Var('x')),
               Seq(Assign('x', Var('y')), Assign('y', Var('t'))))
    post = ImpAnd(Compare('==', Var('x'), Var('b')),
                  Compare('==', Var('y'), Var('a')))
    verify(pre, stmt, post, "Swap")


def test_abs():
    """{ true }  if x<0 then r:=0-x else r:=x  { r >= 0 ∧ (r==x ∨ r==0-x) }"""
    pre = BoolConst(True)
    stmt = If(Compare('<', Var('x'), IntConst(0)),
              Assign('r', BinOp('-', IntConst(0), Var('x'))),
              Assign('r', Var('x')))
    post = ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                  ImpOr(Compare('==', Var('r'), Var('x')),
                        Compare('==', Var('r'), BinOp('-', IntConst(0), Var('x')))))
    verify(pre, stmt, post, "Absolute Value")


# ============================================================================
# Part (c): Invariant Discovery — 8 pts
#
# For each program below, replace the `???` invariant with a correct one.
# [EXPLAIN] in a comment how you found each invariant and why it works.
# ============================================================================

def test_mult():
    """
    Program C1 — Multiplication by addition:
      { a >= 0 }
      i := 0; r := 0;
      while i < a  invariant r == i * b  ∧  i <= a  do
        r := r + b;  i := i + 1;
      { r == a * b }

    # [EXPLAIN] I found the invariant by tracking the loop counter: after i
    # iterations, the loop has added b exactly i times, so r == i * b; I also
    # need i <= a so that when the loop exits, not(i < a) gives i == a.
    # It holds initially because i = 0 and r = 0 (0 = 0 * b --> 0 = 0 and 0 <= a >= 0), and one loop step preserves it
    # because r + b == (i + 1) * b while i < a implies i + 1 <= a.
    # On exit, the invariant plus not(i < a) gives i == a, so r == a * b.
    """
    pre = Compare('>=', Var('a'), IntConst(0))
    inv = ImpAnd(
        Compare('==', Var('r'), BinOp('*', Var('i'), Var('b'))),
        Compare('<=', Var('i'), Var('a'))
    )
    body = Seq(Assign('r', BinOp('+', Var('r'), Var('b'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', IntConst(0)),
                   While(Compare('<', Var('i'), Var('a')), inv, body)))
    post = Compare('==', Var('r'), BinOp('*', Var('a'), Var('b')))
    verify(pre, stmt, post, "C1: Multiplication by Addition")


def test_add():
    """
    Program C2 — Addition by loop:
      { n >= 0 ∧ m >= 0 }
      i := 0; r := n;
      while i < m  invariant r = n + i  ^ i <= m do
        r := r + 1;  i := i + 1;
      { r == n + m }

      # [EXPLAIN] I found the invariant by tracking the loop counter: after i
      # iterations, the loop has added 1 exactly i times, so r == n + i; I also
      # need i <= m so that when the loop exits, not(i < m) gives i == m.
      # It holds initially because i = 0 and r = n (r = n + 0 --> r = n and 0 <= m >= 0), and one
      # loop step preserves it because r + 1 == n + (i + 1) while i < m implies i + 1 <= m.
      # On exit, the invariant plus not(i < m) gives i == m, so r == n + m.
    
    """
    pre = ImpAnd(Compare('>=', Var('n'), IntConst(0)),
                 Compare('>=', Var('m'), IntConst(0)))
    inv = ImpAnd(
        Compare('==', Var('r'), BinOp('+', Var('n'), Var('i'))),
        Compare('<=', Var('i'), Var('m'))
    )
    body = Seq(Assign('r', BinOp('+', Var('r'), IntConst(1))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', Var('n')),
                   While(Compare('<', Var('i'), Var('m')), inv, body)))
    post = Compare('==', Var('r'), BinOp('+', Var('n'), Var('m')))
    verify(pre, stmt, post, "C2: Addition by Loop")


def test_sum():
    """
    Program C3 — Sum of 1..n:
      { n >= 1 }
      i := 1; s := 0;
      while i <= n  invariant 2*s = (i * (i - 1)) ^ i <= n+1 do
        s := s + i;  i := i + 1;
      { 2 * s == n * (n + 1) }

    # [EXPLAIN] I found the invariant by noticing that when the loop counter is i,
    # the loop has already added 1 through i - 1, so 2*s == i*(i - 1); I use this
    # division-free form because the IMP language only has +, -, and *.
    # The invariant holds initially at i = 1, s = 0, and one loop step preserves it
    # because adding i gives 2*(s+i) == i*(i-1)+2*i == (i+1)*i.
    # On exit, i <= n + 1 and not(i <= n) imply i == n + 1, so 2*s == n*(n+1).
    """
    pre = Compare('>=', Var('n'), IntConst(1))
    inv = ImpAnd(
        Compare(
            '==',
            BinOp('*', IntConst(2), Var('s')),
            BinOp('*', Var('i'), BinOp('-', Var('i'), IntConst(1)))
        ),
        Compare('<=', Var('i'), BinOp('+', Var('n'), IntConst(1)))
    )
    body = Seq(Assign('s', BinOp('+', Var('s'), Var('i'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(1)),
               Seq(Assign('s', IntConst(0)),
                   While(Compare('<=', Var('i'), Var('n')), inv, body)))
    post = Compare('==', BinOp('*', IntConst(2), Var('s')),
                   BinOp('*', Var('n'), BinOp('+', Var('n'), IntConst(1))))
    verify(pre, stmt, post, "C3: Sum of 1..n")


# ============================================================================
# Part (d): Find the Bug — 4 pts
#
# The invariant below is WRONG (too weak). Your VCG should report failure.
# 1. Run it — which side VC fails? loop postcondition failds because the invariant is too weak to guarantee the postcondition.
# 2. [EXPLAIN] Give a concrete state where the invariant holds but the
#    postcondition does not.
# 3. Fix the invariant and re-verify.

# [EXPLAIN] The loop postcondition VC fails: the invariant
# q*y + r == x is preserved by the body, but it is too weak to prove 0 <= r
# after the loop exits. For example, x = 5, y = 3, q = 2, r = -1 satisfies
# q*y + r == x and r < y, but violates the postcondition because r < 0.
# Adding r >= 0 to the invariant fixes the proof.
# ============================================================================

def test_buggy_div():
    """
    Integer division with a BUGGY invariant.
      { x >= 0 ∧ y > 0 }
      q := 0; r := x;
      while r >= y  invariant (q * y + r == x)  do    ← TOO WEAK! r = x - yq and r >= 0
        r := r - y;  q := q + 1;
      { q * y + r == x ∧ 0 <= r ∧ r < y }

    The invariant q * y + r == x is correct but INCOMPLETE.
    It is missing a crucial conjunct. Find it.
    """
    pre = ImpAnd(Compare('>=', Var('x'), IntConst(0)),
                 Compare('>', Var('y'), IntConst(0)))

    # BUGGY invariant — intentionally too weak
    inv_buggy = Compare('==',
        BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
        Var('x'))

    body = Seq(Assign('r', BinOp('-', Var('r'), Var('y'))),
               Assign('q', BinOp('+', Var('q'), IntConst(1))))
    stmt = Seq(Assign('q', IntConst(0)),
               Seq(Assign('r', Var('x')),
                   While(Compare('>=', Var('r'), Var('y')),
                         inv_buggy, body)))
    post = ImpAnd(Compare('==',
                       BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
                       Var('x')),
                  ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                         Compare('<', Var('r'), Var('y'))))

    verify(pre, stmt, post, "Buggy Division (should FAIL)")

    # Uncomment and fix the invariant below, then re-verify.
    inv_fixed = ImpAnd(
        Compare('==', BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')), Var('x')),
        Compare('>=', Var('r'), IntConst(0))
    )
    stmt = Seq(Assign('q', IntConst(0)),
               Seq(Assign('r', Var('x')),
                   While(Compare('>=', Var('r'), Var('y')),
                         inv_fixed, body)))
    verify(pre, stmt, post, "FIXED: Verified")


# ============================================================================
# Part (a): WP Derivation via Z3 — 6 pts
#
# Build the following program as an IMP AST:
#   x := x + 1;
#   if x > 0 then y := x * 2 else y := 0 - x;
# Postcondition: { y > 0 }
#
# 1. Call wp() to get the weakest precondition. Print the Z3 formula.
# 2. Use Z3 to check whether each of the following is a valid precondition:
#    - { x >= 0 }
#    - { x >= -1 }
#    - { x == -1 }
#    For each, print whether it's valid and add a comment explaining why.
# ============================================================================

def test_wp_derivation():
    """
    Part (a): Use your VCG to compute wp, then check candidate preconditions.
    """
    print("=== Part (a): WP Derivation ===")

    # Build the IMP AST for the program above
    stmt = Seq(Assign('x', BinOp('+', Var('x'), IntConst(1))), 
               If(Compare('>', Var('x'), IntConst(0)),
                  Assign('y', BinOp('*', Var('x'), IntConst(2))),
                  Assign('y', BinOp('-', IntConst(0), Var('x')))))
    post = Compare('>', Var('y'), IntConst(0))

    # Compute wp(stmt, post_z3) and print it
    wp_result = wp(stmt, bexp_to_z3(post))
    print(f"  wp = {wp_result}")

    # For each candidate precondition, check if pre → wp is valid
    # [EXPLAIN] in a comment: why is this precondition valid or invalid?
    candidates = [
        ("x >= 0",  z3_var('x') >= 0), # VALID: If x is non-negative, then after x := x + 1, x will be positive, so y will be 2*x which is > 0.
        ("x >= -1", z3_var('x') >= -1), # INVALID: If x is -1, then after x := x + 1, x will be 0, so y will be 0 - 0 = 0, which does not satisfy y > 0.
        ("x == -1", z3_var('x') == -1), # INVALID: If x is exactly -1, then after x := x + 1, x will be 0, so y will be 0 - 0 = 0, which does not satisfy y > 0.
    ]
    for name, pre in candidates:
        s = Solver()
        s.add(Not(Implies(pre, wp_result)))
        result = s.check()
        valid = (result == unsat)
        print(f"  {name}: {'VALID' if valid else 'INVALID'}")
    print()


# ============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("Part (b): VCG Correctness Tests")
    print("=" * 60)
    test_swap()
    test_abs()

    print("=" * 60)
    print("Part (a): WP Derivation via Z3")
    print("=" * 60)
    test_wp_derivation()

    print("=" * 60)
    print("Part (c): Invariant Discovery")
    print("=" * 60)
    test_mult()
    test_add()
    test_sum()

    print("=" * 60)
    print("Part (d): Find the Bug")
    print("=" * 60)
    test_buggy_div()
