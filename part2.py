"""
Four numbers game solver

In the second part of the homework, we will implement
a solver for the four numbers game.

=== Four numbers game ===

The game works as follows:
First, I secretly think of two positive integers x and y.
I don't tell you what they are, but instead I give you four
numbers:
    a, b, c, d
and tell you that they are the values of the sum, difference,
product, and quotient (x+y, x-y, xy, and x/y), in an unknown order.
Assume that the difference is nonnegative and the quotient is a whole number.

Can you figure out what x and y are?

=== Examples ===

Four numbers: 20, 95, 105, 500
Solution: x = 100, y = 5.

Four numbers: 2, 6, 18, 72
Solution: x = 12, y = 6.

Four numbers: 0, 1, 1, 2
Solution: x = 1, y = 1.

=== Input ===

Your solver should take 4 numbers as input from the user.
For simplicity, assume that all 4 numbers are nonnegative integers.
You can get input in Python using the `input` function:
    num1 = int(input("First number: "))

=== Output, Stage 1 ===

Use Z3 to output the
solution (x and y), if it finds one,
or say that there are no solutions.
You can assume that x and y are positive integers.

The first function

    solve_stage1(a, b, c, d)

should, when given four integers a, b, c, d, return a solution

    x, y

if there is at least one solution, or None if there is no solution.

Second, the function

    run_interactive()

should provide an interactive version: it should prompt the user for 4 numbers, then display as output the correct answers x and y.
It should use an auxiliary function `get_input()` to get the input from the user.

=== Output, Stage 2 ===

Use Z3 to determine whether there are any *other* solutions, besides
the one that you found in the first stage.

The function

    solve_stage2(a, b, c, d, x, y)

should return a Python string

    "multiple", "unique", or "none"

depending on whether multiple solutions exist.
The arguments x and y should be the answer from stage1,
or x = None, y = None if stage1 returns None.

Update your run_interactive() version to also show the output of solve_stage2.

=== Helper function ===

Please use the helper function get_solution
in helper.py that will be useful for this part.
If the spec is satisfiable (SAT), it will return
a solution that you can use to get the values of x and y:
    x = Int('x')
    x_val = get_solution(spec)[x]

=== Try it out! ===

Try out your game by running
    python3 part2.py

to see if it works!

If you like, you can also write unit tests, but this
is not required for this part.
"""

import z3
import pytest

from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

def get_input():
    a = int(input("First number: "))
    b = int(input("Second number: "))
    c = int(input("Third number: "))
    d = int(input("Fourth number: "))
    return a, b, c, d
    # raise NotImplementedError

def solve_stage1(a, b, c, d):
    x_val = z3.Int('x_val')
    y_val = z3.Int('y_val')

    a_c = z3.IntVal(a)
    b_c = z3.IntVal(b)
    c_c = z3.IntVal(c)
    d_c = z3.IntVal(d)

    domain_constraints = z3.And(
        x_val > 0,
        y_val > 0,
        x_val >= y_val,
        x_val % y_val == 0
    )

    exprs = [
        x_val + y_val,
        x_val - y_val,
        x_val * y_val,
        x_val / y_val
    ]

    match_constraints = z3.And(
        z3.Or([a_c == e for e in exprs]),
        z3.Or([b_c == e for e in exprs]),
        z3.Or([c_c == e for e in exprs]),
        z3.Or([d_c == e for e in exprs]),
    )

    spec = z3.And(domain_constraints, match_constraints)

    if solve(spec) != SAT:
        return None

    model = get_solution(spec)
    return model[x_val].as_long(), model[y_val].as_long()
    # raise NotImplementedError

def run_interactive():
    print("=== Input ===")
    a, b, c, d = get_input()
    print("=== Stage 1 ===")
    # TODO, call your solution for Stage 1, print the solution
    result = solve_stage1(a, b, c, d)
    if result is None:
        print("No solution found.")
        x, y = None, None
    else:
        x, y = result
        print(f"Solution: x = {x}, y = {y}")
    print("=== Stage 2 ===")
    # TODO: after you complete Stage 2,
    status = solve_stage2(a, b, c, d, x, y)
    print(f"Solution status: {status}")

    # raise NotImplementedError

def solve_stage2(a, b, c, d, x, y):
    # TODO: Determine if there are any other solutions
    # Return "multiple", "unique", or "none"
    if x is None or y is None:
        return "none"

    x_alt = z3.Int('x_alt')
    y_alt = z3.Int('y_alt')
    a_c = z3.IntVal(a)
    b_c = z3.IntVal(b)
    c_c = z3.IntVal(c)
    d_c = z3.IntVal(d)

    domain_constraints = z3.And(
        x_alt > 0,
        y_alt > 0,
        x_alt >= y_alt,
        x_alt % y_alt == 0
    )
    exprs = [
        x_alt + y_alt,
        x_alt - y_alt,
        x_alt * y_alt,
        x_alt / y_alt
    ]

    match_constraints = z3.And(
        z3.Or([a_c == e for e in exprs]),
        z3.Or([b_c == e for e in exprs]),
        z3.Or([c_c == e for e in exprs]),
        z3.Or([d_c == e for e in exprs]),
    )

    different_solution = z3.Not(
        z3.And(x_alt == x, y_alt == y)
    )

    spec = z3.And(domain_constraints, match_constraints, different_solution)

    if solve(spec) == SAT:
        return "multiple"
    else:
        return "unique"

    # raise NotImplementedError

if __name__ == "__main__":
    run_interactive()
