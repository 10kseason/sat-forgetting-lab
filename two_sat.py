"""A dependency-free 2-SAT solver. Variables are numbered from 1."""


def solve_2cnf(n, clauses, units=()):
    """Return a Boolean tuple in variable order, or None for UNSAT."""
    if n < 0:
        raise ValueError("negative variable count")
    graph = {v: [] for i in range(1, n + 1) for v in (i, -i)}
    reverse = {v: [] for v in graph}

    def edge(a, b):
        graph[a].append(b)
        reverse[b].append(a)

    def insert(clause):
        if len(clause) > 2 or any(abs(v) > n or v == 0 for v in clause):
            raise ValueError("expected a clause of at most two in-range literals")
        if not clause:
            return False
        a, b = clause[0], clause[-1]
        edge(-a, b)
        edge(-b, a)
        return True

    if not all(insert(c) for c in clauses) or not all(insert((v,)) for v in units):
        return None
    seen = set()
    order = []
    for v in graph:
        if v in seen:
            continue
        seen.add(v)
        stack = [(v, iter(graph[v]))]
        while stack:
            node, outgoing = stack[-1]
            nxt = next(outgoing, None)
            if nxt is None:
                order.append(node)
                stack.pop()
            elif nxt not in seen:
                seen.add(nxt)
                stack.append((nxt, iter(graph[nxt])))
    component = {}
    for index, v in enumerate(reversed(order)):
        if v in component:
            continue
        stack = [v]
        component[v] = index
        while stack:
            for nxt in reverse[stack.pop()]:
                if nxt not in component:
                    component[nxt] = index
                    stack.append(nxt)
    if any(component[v] == component[-v] for v in range(1, n + 1)):
        return None
    return tuple(component[v] > component[-v] for v in range(1, n + 1))
