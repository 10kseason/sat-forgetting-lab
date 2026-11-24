"""Exact existential projection for CNFs dual-Horn on their hidden variables."""

from collections import deque
from dataclasses import dataclass
from itertools import product
from math import prod

from two_sat import solve_2cnf


def clause_value(clause, assignment):
    return any(assignment[abs(lit) - 1] == (lit > 0) for lit in clause)


def cnf_value(clauses, assignment):
    return all(clause_value(clause, assignment) for clause in clauses)


def canonical(clause):
    literals = set(clause)
    if any(-lit in literals for lit in literals):
        return None  # True
    return tuple(sorted(literals, key=lambda lit: (abs(lit), lit)))


@dataclass(frozen=True)
class Projection:
    clauses: tuple
    policies_examined: int
    policy_bound: int
    rules_before: int
    rules_after: int


class HiddenCNF:
    """Background 2-CNF on retained variables, plus clauses with ≤1 negative hidden literal."""

    def __init__(self, retained, hidden, clauses, background=()):
        if min(retained, hidden) < 0:
            raise ValueError("negative variable count")
        self.retained = retained
        self.total = retained + hidden
        self.heads = range(retained + 1, self.total + 1)
        self.background = tuple(tuple(c) for c in background)
        if any(len(c) > 2 or any(v == 0 or abs(v) > retained for v in c)
               for c in self.background):
            raise ValueError("the background must be 2-CNF on retained variables")
        self.rules = {h: [] for h in self.heads}
        self.goals = []
        for raw in clauses:
            raw = tuple(raw)
            if any(v == 0 or abs(v) > self.total for v in raw):
                raise ValueError("literal index out of range")
            clause = canonical(raw)
            if clause is None:
                continue
            neg = [lit for lit in clause if lit < -retained]
            if len(neg) > 1:
                raise ValueError("more than one negative hidden literal")
            if neg:
                self.rules[-neg[0]].append(tuple(v for v in clause if v != neg[0]))
            else:
                self.goals.append(clause)

    def greatest(self, fixed):
        """Greatest feasible hidden vector for the upper bounds alone."""
        if len(fixed) != self.retained:
            raise ValueError("wrong retained assignment length")
        current = (True,) * len(self.heads)
        while True:
            values = tuple(fixed) + current
            updated = tuple(cnf_value(self.rules[h], values) for h in self.heads)
            if updated == current:
                return current
            current = updated

    def extend(self, fixed):
        """Return a complete satisfying assignment extending fixed, or None."""
        if len(fixed) != self.retained:
            raise ValueError("wrong retained assignment length")
        fixed = tuple(fixed)
        if not cnf_value(self.background, fixed):
            return None
        values = fixed + self.greatest(fixed)
        return values if cnf_value(self.goals, values) else None

    def representatives(self):
        """Keep tails minimal under implication modulo the fixed background."""
        def implies(left, right):
            if set(left).issubset(right):
                return True
            # A counterexample makes some left literal true and every right literal false.
            off = tuple(-v for v in right)
            return all(solve_2cnf(self.total, self.background, (*off, v)) is None
                       for v in left)

        kept = {}
        for h in self.heads:
            result = []
            for tail in self.rules[h]:
                if any(implies(old, tail) for old in result):
                    continue
                result = [old for old in result if not implies(tail, old)]
                result.append(tail)
            kept[h] = result
        return kept

    def _cone(self, goal, rules):
        seen = set()
        todo = [v for v in goal if v > self.retained]
        while todo:
            v = todo.pop()
            if v not in seen:
                seen.add(v)
                todo.extend(w for tail in rules[v] for w in tail if w > self.retained)
        return tuple(sorted(seen))

    def _selected_clause(self, goal, selected):
        """Flatten the OR graph reachable under one fixed choice per head."""
        literals = {v for v in goal if v <= self.retained}
        todo = [v for v in goal if v > self.retained]
        successors = {}
        while todo:
            v = todo.pop()
            if v in successors:
                continue
            tail = selected[v]
            if tail is None:
                return None  # This reachable head has no upper bound.
            successors[v] = [w for w in tail if w > self.retained]
            literals.update(w for w in tail if w <= self.retained)
            todo.extend(successors[v])
        indegree = dict.fromkeys(successors, 0)
        for outgoing in successors.values():
            for w in outgoing:
                indegree[w] += 1
        queue = deque(w for w in successors if not indegree[w])
        visited = 0
        while queue:
            visited += 1
            for w in successors[queue.popleft()]:
                indegree[w] -= 1
                if not indegree[w]:
                    queue.append(w)
        if visited < len(successors):
            return None  # A reachable directed cycle can support itself.
        return canonical(literals)

    def project(self, max_policies=None):
        """Produce a retained-variable CNF, optionally bounding policy enumeration."""
        before = sum(map(len, self.rules.values()))
        if solve_2cnf(self.retained, self.background) is None:
            return Projection(((),), 0, 0, before, 0)
        rules = self.representatives()
        tasks = [(goal, self._cone(goal, rules)) for goal in self.goals]
        bound = sum(prod(max(1, len(rules[h])) for h in cone) for _, cone in tasks)
        if max_policies is not None and bound > max_policies:
            raise ValueError(f"requires {bound} policies, budget is {max_policies}")
        found = set(self.background)
        examined = 0
        for goal, cone in tasks:
            for choice in product(*(rules[h] or (None,) for h in cone)):
                examined += 1
                clause = self._selected_clause(goal, dict(zip(cone, choice)))
                if clause is not None:
                    found.add(clause)
        return Projection(tuple(sorted(found, key=lambda c: (len(c), c))), examined, bound,
                          before, sum(map(len, rules.values())))
