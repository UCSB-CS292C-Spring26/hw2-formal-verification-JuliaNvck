"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
#
# Encode rules R1–R5 from the README as Z3 constraints.
#
# You must design the encoding yourself. Consider:
# - Use ForAll to make rules apply to all users/resources.
# - Encode both what IS allowed and what is NOT allowed.
# - Rule R4 overrides R3 — handle this carefully.
#
# Return a list of Z3 constraints.
# ============================================================================

def make_policy(include_r4=True):
    """
    Return a list of Z3 constraints encoding rules R1–R5.

    1. How to express "viewers may ONLY do X" (everything else is denied).
    2. How R4 overrides R3 for admins.
    3. Whether you need a closed-world assumption (if not explicitly
       allowed, it's denied).
    """
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = []

    # Encode R1–R5
    # Viewers may only file_read non-sensitive resources.
    constraints.append(
        ForAll([u, r],
            Implies(
                And(role(u) == VIEWER, Not(is_sensitive(r))),
                allowed(u, FILE_READ, r)
            )
        )
    )

    constraints.append(
        ForAll([u, r],
            Implies(
                And(role(u) == VIEWER, is_sensitive(r)),
                Not(allowed(u, FILE_READ, r))
            )
        )
    )

    constraints.append(
        ForAll([u, r],
            Implies(
                role(u) == VIEWER,
                And(
                    Not(allowed(u, FILE_WRITE, r)),
                    Not(allowed(u, SHELL_EXEC, r)),
                    Not(allowed(u, NETWORK_FETCH, r))
                )
            )
        )
    )

    # Developers may file_read anything and file_write resources they own or that are in the sandbox.
    constraints.append(
        ForAll([u, r],
            Implies(
                role(u) == DEVELOPER,
                And(
                    allowed(u, FILE_READ, r),
                    Implies(
                        Or(owner(r) == u, in_sandbox(r)),
                        allowed(u, FILE_WRITE, r),
                    )
                )
            )
        )
    )

    constraints.append(
        ForAll([u, r],
            Implies(
                And(role(u) == DEVELOPER, Not(Or(owner(r) == u, in_sandbox(r)))),
                Not(allowed(u, FILE_WRITE, r))
            )
        )
    )

    constraints.append(
        ForAll([u, r],
            Implies(
                role(u) == DEVELOPER,
                And(
                    Not(allowed(u, SHELL_EXEC, r)),
                    Not(allowed(u, NETWORK_FETCH, r))
                )
            )
        )
    )

    # Admins may use any tool on any resource.
    constraints.append(
        ForAll([u, r],
            Implies(
                role(u) == ADMIN,
                And(
                    allowed(u, FILE_READ, r),
                    allowed(u, FILE_WRITE, r),
                    Implies(Not(is_sensitive(r)), allowed(u, SHELL_EXEC, r)),
                    Implies(in_sandbox(r), allowed(u, NETWORK_FETCH, r))
                )
            )
        )
    )


    # Nobody may shell_exec on sensitive resources (overrides R3).
    if include_r4:
        constraints.append(
            ForAll([u, r],
                Implies(
                    is_sensitive(r),
                    Not(allowed(u, SHELL_EXEC, r))
                )
            )
        )

    # network_fetch is allowed only on sandbox resources.
    constraints.append(
        ForAll([u, r],
            Implies(
                Not(in_sandbox(r)),
                Not(allowed(u, NETWORK_FETCH, r))
            )
        )
    )

    return constraints


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For query 4, also demonstrate what becomes possible without R4.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u = Const('u', User)
    r = Const('r', Resource)

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    query(
        "Q1: Can a developer write to a sensitive file they don't own, in the sandbox?",
        policy,
        And(
            role(u) == DEVELOPER,
            is_sensitive(r),
            Not(owner(r) == u),
            in_sandbox(r),
            allowed(u, FILE_WRITE, r)
        )
    )

    # This is SAT because the policy allows developers to write to sandbox resources, even if they are sensitive and not owned by the developer.

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    query(
        "Q2: Can an admin network_fetch a resource outside the sandbox?",
        policy,
        And(
            role(u) == ADMIN,
            Not(in_sandbox(r)),
            allowed(u, NETWORK_FETCH, r)
        )
    )

    # This is UNSAT because the policy explicitly states that network_fetch is only allowed on sandbox resources, even for admins.

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    query(
        "Q3: Is there ANY role that can shell_exec on a sensitive resource?",
        policy,
        And(
            is_sensitive(r),
            allowed(u, SHELL_EXEC, r)
        )
    )

    # This is UNSAT because the policy explicitly states that nobody may shell_exec on sensitive resources.

    # Q4: [EXPLAIN] in a comment Remove R4 — what dangerous action becomes possible?
    # Create a modified policy without R4, demonstrate the new capability.
    policy_without_r4 = make_policy(include_r4=False)
    query(
        "Q4: Without R4, can an admin shell_exec on a sensitive resource?",
        policy_without_r4,
        [
            role(u) == ADMIN,
            is_sensitive(r),
            allowed(u, SHELL_EXEC, r)
        ]
    )

    # This is SAT because without R4, the constraint that nobody may shell_exec on sensitive resources is removed, allowing admins to shell_exec on sensitive resources, which could lead to privilege escalation or data breaches if the sensitive resource contains critical information or controls.``



# ============================================================================
# Part (c): Privilege Escalation — 7 pts
#
# New rule R6: Developers may shell_exec on non-sensitive sandbox resources.
#
# Attack scenario: A developer uses shell_exec on a non-sensitive sandbox
# resource to change ANOTHER resource's sensitivity flag (e.g., modifying
# a config file that controls access). This makes a previously sensitive
# resource become non-sensitive, bypassing R4 on the next step.
#
# Model this as a 2-step trace where a resource's sensitivity changes
# between steps.
# ============================================================================

def part_c():
    """
    TODO:
    1. Add rule R6 to the policy.
    2. Model a 2-step trace:
       - Step 1: developer calls shell_exec on resource r1
         (r1 is non-sensitive and in sandbox — allowed by R6)
         Side-effect: this command changes resource r2 from sensitive to
         non-sensitive (e.g., modifying an access-control config)
       - Step 2: developer calls shell_exec on resource r2
         (r2 is NOW non-sensitive — was it allowed before? is it allowed now?)
    3. The twist: r2's sensitivity changes BETWEEN steps. Encode this by
       using two copies of is_sensitive (before and after).
    4. Check if the developer can effectively access a previously-sensitive resource.
    5. [EXPLAIN] in a comment: Propose and implement a fix.
    """
    print("=== Part (c): Privilege Escalation ===\n")

    # TODO: Your encoding here.
    # Hint: Use is_sensitive_before and is_sensitive_after as two separate
    # functions, or use a time-indexed model.

    print("  TODO: Implement escalation analysis")
    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
