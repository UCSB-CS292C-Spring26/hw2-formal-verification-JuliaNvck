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

    valid_role = ForAll([u],
        Or(role(u) == ADMIN, role(u) == DEVELOPER, role(u) == VIEWER)
    )

    viewer_allow = And(
        role(u) == VIEWER,
        t == FILE_READ,
        Not(is_sensitive(r))
    )

    developer_allow = And(
        role(u) == DEVELOPER,
        Or(
            t == FILE_READ,
            And(
                t == FILE_WRITE,
                Or(owner(r) == u, in_sandbox(r))
            )
        )
    )

    admin_allow = And(
        role(u) == ADMIN,
        Or(
            t == FILE_READ,
            t == FILE_WRITE,
            t == SHELL_EXEC,
            t == NETWORK_FETCH
        )
    )

    # Closed-world policy: allowed is true exactly for rule-authorized actions,
    # after global deny overrides are applied.
    base_allow = Or(viewer_allow, developer_allow, admin_allow)
    valid_tool = And(t >= FILE_READ, t <= NETWORK_FETCH)
    overrides = [Not(And(t == NETWORK_FETCH, Not(in_sandbox(r))))]
    if include_r4:
        overrides.append(Not(And(t == SHELL_EXEC, is_sensitive(r))))

    exact_policy = ForAll([u, t, r],
        allowed(u, t, r) == And(
            valid_tool,
            base_allow,
            *overrides
        )
    )

    return [valid_role, exact_policy]


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

    # This is SAT because without R4, the constraint that nobody may shell_exec on sensitive resources is removed, allowing admins to shell_exec on sensitive resources, which could lead to privilege escalation or data breaches if the sensitive resource contains critical information or controls.



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

    u = Const('u_c', User)
    r = Const('r_c', Resource)
    is_sensitive_before = Function('is_sensitive_before', Resource, BoolSort())
    is_sensitive_after = Function('is_sensitive_after', Resource, BoolSort())
    allowed_before = Function('allowed_before', User, IntSort(), Resource, BoolSort())
    allowed_after = Function('allowed_after', User, IntSort(), Resource, BoolSort())
    r1 = Const('r1', Resource)
    r2 = Const('r2', Resource)

    trace_policy = [
        ForAll([u], Or(role(u) == ADMIN, role(u) == DEVELOPER, role(u) == VIEWER)),

        # R6 before step 1: developers may shell_exec on non-sensitive sandbox resources.
        ForAll([u, r],
            Implies(
                And(role(u) == DEVELOPER, Not(is_sensitive_before(r)), in_sandbox(r)),
                allowed_before(u, SHELL_EXEC, r)
            )
        ),
        # R4 before step 1: nobody may shell_exec on sensitive resources.
        ForAll([u, r],
            Implies(
                is_sensitive_before(r),
                Not(allowed_before(u, SHELL_EXEC, r))
            )
        ),

        # R6 after step 1: developers may shell_exec on resources that are now
        # non-sensitive and sandboxed.
        ForAll([u, r],
            Implies(
                And(role(u) == DEVELOPER, Not(is_sensitive_after(r)), in_sandbox(r)),
                allowed_after(u, SHELL_EXEC, r)
            )
        ),
        # R4 after step 1: the sensitive-resource shell_exec ban still applies.
        ForAll([u, r],
            Implies(
                is_sensitive_after(r),
                Not(allowed_after(u, SHELL_EXEC, r))
            )
        ),
    ]

    # Step 1: developer can shell_exec on non-sensitive sandbox r1.
    step1_allowed = And(
        role(u) == DEVELOPER,
        Not(is_sensitive_before(r1)),
        in_sandbox(r1),
        allowed_before(u, SHELL_EXEC, r1)
    )

    # Side effect: r2 was sensitive before, but is made non-sensitive after.
    side_effect = And(
        r1 != r2,
        is_sensitive_before(r2),
        Not(is_sensitive_after(r2))
    )

    # R6 after step 2: because r2 is now non-sensitive and sandboxed,
    # developer can shell_exec on r2.
    step2_allowed = And(
        role(u) == DEVELOPER,
        Not(is_sensitive_after(r2)),
        in_sandbox(r2),
        allowed_after(u, SHELL_EXEC, r2)
    )

    attack = And(
        step1_allowed,
        Not(allowed_before(u, SHELL_EXEC, r2)),
        side_effect,
        step2_allowed
    )

    result = query(
        "Can a developer bypass R4 by changing r2 from sensitive to non-sensitive?",
        trace_policy,
        attack
    )

    # [EXPLAIN] The bug is that R4 checks whether a resource is sensitive at
    # the moment shell_exec is called, but it does not protect the metadata that
    # controls sensitivity. A developer can use shell_exec on an allowed sandbox
    # resource to modify a config file, causing another resource to no longer be
    # marked sensitive. Then the second shell_exec is allowed because the target
    # appears non-sensitive after the metadata change.
    #
    # Fix: developer shell_exec must not declassify resources. If a developer
    # runs shell_exec, then any resource that was sensitive before the command
    # must still be sensitive afterward.
    fix = Implies(
        step1_allowed,
        ForAll([r],
            Implies(
                is_sensitive_before(r),
                is_sensitive_after(r)
            )
        )
    )

    fixed_result = query(
        "After the fix, can the developer still bypass R4?",
        trace_policy + [fix],
        attack
    )

    if result == sat and fixed_result == unsat:
        print("  ESCALATION BLOCKED")
    else:
        print("  Fix did not block the escalation as expected")

    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
