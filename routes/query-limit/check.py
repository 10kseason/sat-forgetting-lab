"""Check the rail functions, their encodings, and the finite query game."""

from fractions import Fraction
from itertools import combinations
from math import ceil


def reference(n, assignment):
    return all((assignment >> (2 * i)) & 3 for i in range(n))


def chosen_rails(n, secret):
    return tuple(2 * i + ((secret >> i) & 1) + 1 for i in range(n))


def evaluate_clause(clause, assignment):
    return any(
        bool((assignment >> (abs(literal) - 1)) & 1) == (literal > 0)
        for literal in clause
    )


def envelope(models, variables):
    literals = tuple(range(-variables, 0)) + tuple(range(1, variables + 1))
    candidates = [()]
    candidates += [(literal,) for literal in literals]
    candidates += [pair for pair in combinations(literals, 2) if pair[0] != -pair[1]]
    return {
        frozenset(clause)
        for clause in candidates
        if all(evaluate_clause(clause, assignment) for assignment in models)
    }


def encoding(n, selected=()):
    pairs = [(2 * i + 1, 2 * i + 2) for i in range(n)]
    if not selected:
        return pairs, 0
    hidden = tuple(range(2 * n + 1, 3 * n - 1))
    chain = [(selected[0], selected[1], hidden[0])]
    for i, (source, target) in enumerate(zip(hidden, hidden[1:])):
        chain.append((-source, selected[i + 2], target))
    chain.append((-hidden[-1], selected[-1]))
    clauses = pairs + chain
    assert len(clauses) == 2 * n - 1
    for clause in clauses:
        assert len(clause) <= 3 and sum(literal < 0 for literal in clause) <= 1
        for source in (-literal for literal in clause if literal < -2 * n):
            assert all(source < target for target in clause if target > 2 * n)
    return clauses, len(hidden)


def projected_models(clauses, visible, hidden):
    models = set()
    for assignment in range(1 << visible):
        for witness in range(1 << hidden):
            full = assignment | (witness << visible)
            if all(evaluate_clause(clause, full) for clause in clauses):
                models.add(assignment)
                break
    return models


def check_functions():
    oracles = 0
    projected_encodings = 0
    for n in range(3, 7):
        models = {
            assignment for assignment in range(1 << (2 * n))
            if reference(n, assignment)
        }
        base_clauses, hidden = encoding(n)
        expected_envelope = {frozenset(clause) for clause in base_clauses}
        assert envelope(models, 2 * n) == expected_envelope
        assert projected_models(base_clauses, 2 * n, hidden) == models
        differences = set()
        for secret in range(1 << n):
            rails = chosen_rails(n, secret)
            long_clause_models = {
                assignment for assignment in models if evaluate_clause(rails, assignment)
            }
            defect = models - long_clause_models
            assert len(defect) == 1
            (row,) = defect
            assert row.bit_count() == n
            differences.add(row)
            assert envelope(long_clause_models, 2 * n) == expected_envelope
            if n <= 5:
                clauses, hidden = encoding(n, rails)
                assert projected_models(clauses, 2 * n, hidden) == long_clause_models
                projected_encodings += 1
            oracles += 1
        assert len(differences) == 1 << n
        print(f"rail_functions n={n} secrets={len(differences)} reference_models={len(models)}")
    print(f"distinct_defect_and_signed_envelope_checks={oracles}")
    print(f"punctured_CNF_projections_checked={projected_encodings}")


def outcome(probes, fallback_reference, defect):
    for count, probe in enumerate(probes, start=1):
        if probe == defect:
            return False, count
    return fallback_reference, len(probes)


def deterministic_points(rows, cap):
    points = set()
    for count in range(cap + 1):
        for probes in combinations(range(rows), count):
            for fallback in (False, True):
                accept_reference, _ = outcome(probes, fallback, None)
                missed = sum(outcome(probes, fallback, defect)[0] for defect in range(rows))
                points.add((Fraction(not accept_reference), Fraction(missed, rows)))
    return points


def exact_minimax(points):
    # Minimize the maximum coordinate over the convex hull of two-error points.
    # An optimum occurs at a vertex or where a hull edge crosses the diagonal.
    best = min(max(point) for point in points)
    for first, second in combinations(points, 2):
        first_side = first[0] - first[1]
        second_side = second[0] - second[1]
        if first_side * second_side < 0:
            weight = first_side / (first_side - second_side)
            diagonal = (1 - weight) * first[0] + weight * second[0]
            best = min(best, diagonal)
    return best


def measured_errors_and_cost(rows, weighted_strategies):
    errors = []
    costs = []
    for defect in (None, *range(rows)):
        error = Fraction(0)
        cost = Fraction(0)
        for weight, probes, fallback in weighted_strategies:
            reference_guess, count = outcome(probes, fallback, defect)
            if reference_guess != (defect is None):
                error += weight
            cost += weight * count
        errors.append(error)
        costs.append(cost)
    return max(errors), max(costs)


def check_query_game():
    rows = 8
    optimal_errors = [
        exact_minimax(deterministic_points(rows, cap)) for cap in range(rows + 1)
    ]
    assert optimal_errors == [Fraction(rows - cap, 2 * rows - cap) for cap in range(rows + 1)]
    assert optimal_errors.index(0) == rows
    error_cases = {*optimal_errors, Fraction(1, 8), Fraction(2, 5), Fraction(49, 100)}
    for error in sorted(error_cases):
        cap = min(i for i, achievable in enumerate(optimal_errors) if achievable <= error)
        assert cap == ceil(rows * (1 - 2 * error) / (1 - error))

        subsets = list(combinations(range(rows), cap))
        bounded = [(error, (), False)]
        bounded += [((1 - error) / len(subsets), probes, True) for probes in subsets]
        measured_error, _ = measured_errors_and_cost(rows, bounded)
        assert measured_error <= error

        expected = [(error, (), False), (error, (), True), (1 - 2 * error, range(rows), True)]
        measured_error, measured_cost = measured_errors_and_cost(rows, expected)
        assert measured_error == error
        assert measured_cost == rows * (1 - 2 * error)
    fractions = ", ".join(map(str, optimal_errors))
    print(f"query_game rows={rows} worst_case_cap_errors=[{fractions}]")
    print(f"matching_strategies_exact_rational_error_cases={len(error_cases)}")


if __name__ == "__main__":
    check_functions()
    check_query_game()
