"""
CS292C Homework 2 — Problem 1: Z3 Warm-Up + EUF Puzzle (15 points)
===================================================================
Complete each function below. Run this file to check your answers.
"""

from z3 import *


# ---------------------------------------------------------------------------
# Part (a) — 3 pts
# Find integers x, y, z such that x + 2y = z, z > 10, x > 0, y > 0.
# ---------------------------------------------------------------------------
def part_a():
    x, y, z = Ints('x y z')
    s = Solver()

    s.add(x + 2*y == z)
    s.add(z > 10)
    s.add(x > 0)
    s.add(y > 0)

    print("=== Part (a) ===")
    if s.check() == sat:
        m = s.model()
        print(f"SAT: x={m[x]}, y={m[y]}, z={m[z]}")
    else:
        print("UNSAT (unexpected!)")
    print()


# ---------------------------------------------------------------------------
# Part (b) — 3 pts
# Prove validity of: ∀x. x > 5 → x > 3
# Hint: A formula F is valid iff ¬F is unsatisfiable.
# ---------------------------------------------------------------------------
def part_b():
    x = Int('x')
    s = Solver()

    # Add the *negation* of the formula and check UNSAT
    s.add(Not(Implies(x > 5, x > 3)))

    print("=== Part (b) ===")
    result = s.check()
    if result == unsat:
        print("Valid! (negation is UNSAT)")
    else:
        print(f"Not valid — counterexample: {s.model()}")
    print()


# ---------------------------------------------------------------------------
# Part (c) — 5 pts: The EUF Puzzle
#
# Formula:  f(f(x)) = x  ∧  f(f(f(x))) = x  ∧  f(x) ≠ x
#
# STEP 1: Check satisfiability with Z3. (2 pts)
#
# STEP 2: Use Z3 to derive WHY the result holds. (3 pts)
#   Write a series of Z3 validity checks that demonstrate the key reasoning
#   steps. For example, from f(f(x)) = x, what can you derive about f(f(f(x)))?
#   Each check should print what it's testing and whether it holds.
#   Hint: Apply f to both sides of the first equation.
# ---------------------------------------------------------------------------
def part_c():
    S = DeclareSort('S')
    x = Const('x', S)
    f = Function('f', S, S)
    s = Solver()

    # Add the three constraints
    s.add(f(f(x)) == x)
    s.add(f(f(f(x))) == x)
    s.add(f(x) != x)

    print("=== Part (c) ===")
    result = s.check()
    if result == sat:
        print(f"SAT: {s.model()}")
    else:
        print("UNSAT")
    # Add Z3 derivation steps below (see STEP 2 above).
    print("Derivation steps:")
    # Derivation step 1:
    # If f(f(x)) = x, then applying f to both sides gives
    # f(f(f(x))) = f(x).
    s1 = Solver()
    step1 = Implies(f(f(x)) == x, f(f(f(x))) == f(x))
    s1.add(Not(step1)) # Negate the implication to check validity
    print(
        "Check 1: f(f(x)) = x implies f(f(f(x))) = f(x):",
        "Valid" if s1.check() == unsat else "INVALID"
    )
    # Derivation step 2:
    # If f(f(f(x))) equals both f(x) and x, then f(x) = x.
    s2 = Solver()
    step2 = Implies(And(f(f(f(x))) == f(x), f(f(f(x))) == x), f(x) == x)
    s2.add(Not(step2))
    print(
        "Check 2: f(f(f(x))) = f(x) and f(f(f(x))) = x implies f(x) = x:",
        "Valid" if s2.check() == unsat else "INVALID"
    )
    # Derivation step 3:
    # The original constraints force f(x) = x, but also require f(x) != x.
    s3 = Solver()
    s3.add(f(f(f(x))) == f(x), f(f(f(x))) == x, f(x) != x)
    print(
        "Check 3: f(f(f(x))) == f(x), f(f(f(x))) == x, f(x) != x: derived equality contradicts f(x) != x:",
        "Valid contradiction, unsat" if s3.check() == unsat else "INVALID"
    )
    print()


# ---------------------------------------------------------------------------
# Part (d) — 4 pts: Array Axioms
#
# Prove BOTH axioms (two separate solver checks):
#   (1) Read-over-write HIT:   i = j  →  Select(Store(a, i, v), j) = v
#   (2) Read-over-write MISS:  i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
#
# [EXPLAIN] in a comment below: Why are these two axioms together sufficient
# to fully characterize Store/Select behavior? (2–3 sentences)
# Explanation:
# The two axioms together capture the essential behavior of arrays under the Store and Select operations, where Store updates the value at a specific index while leaving all other indices unchanged and Select retrieves correct values from the array.
# Axiom (1) states that if we store a value v at index i and then select from the same index j (where j = i), we should get back the value v, which captures the "hit" case. 
# Axiom (2) states that if we select from a different index j (where j ≠ i), we should get the value that was originally at index j before the store operation, which captures the "miss" case.
# ---------------------------------------------------------------------------
def part_d():
    a = Array('a', IntSort(), IntSort())
    i, j, v = Ints('i j v')

    print("=== Part (d) ===")

    # Axiom 1: Read-over-write HIT
    s1 = Solver()
    # Negate axiom 1 and check UNSAT
    s1.add(Not(Implies(i == j, Select(Store(a, i, v), j) == v)))
    r1 = s1.check()
    print(f"Axiom 1 (hit):  {'Valid' if r1 == unsat else 'INVALID'}")

    # Axiom 2: Read-over-write MISS
    s2 = Solver()
    # Negate axiom 2 and check UNSAT
    s2.add(Not(Implies(i != j, Select(Store(a, i, v), j) == Select(a, j))))
    r2 = s2.check()
    print(f"Axiom 2 (miss): {'Valid' if r2 == unsat else 'INVALID'}")
    print()


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
