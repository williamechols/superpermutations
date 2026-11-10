"""Python mirror of `LowerBounds/SSearch.lean`: the same functions on the same numbers, the
children of a state in the same order.  Used by `s_plan.py` to cut a search into kernel-sized parts and for
cross-checks.  Nothing computed here is trusted by Lean: every generated lemma is checked by `decide +kernel`, and
a wrong mirror makes a lemma fail.

A state is (y, P, N, f); the tree of used classes is kept outside, as one Python set that the caller updates along
the current path (`added` of a child = the class names its piece adds).
"""

M1 = 0x1111111111111111
M7 = 0x7777777777777777
M8 = 0x8888888888888888


def pw(n):
    return 16 ** n


def idc(n):
    c = 0
    for i in range(1, n + 1):
        c = c * 16 + i
    return c


def exc(k, c):
    return (c % 16) * pw(k - 1) + c // 16


def doorc(k, x):
    return (x % pw(k - 2)) * 256 + ((x // pw(k - 2)) % 16) * 16 + x // pw(k - 1)


def rotl(k, c, i):
    return (c % pw(k - i)) * pw(i) + c // pw(k - i)


def log2(m):
    return m.bit_length() - 1 if m > 0 else 0


def pos(k, c):
    x = c ^ (k * M1)
    z = ((x & M7) + M7) | x
    m = (z & M8) ^ M8
    return log2(m) // 4


def canon(k, c):
    return rotl(k, c, max(k - 1 - pos(k, c), 0))


def kid(A, q2, C2, P, N, f, d, x):
    """the state after a piece of deficit d with exit x, or None"""
    if d == 0:
        return None if f == 1 else (x, P, N + q2, 0)
    if N + q2 + C2 <= P + A * d:
        return None
    if f == 0:
        return None if N <= P else (x, P + A * d, N + q2, 2 if 2 <= d else 1)
    return (x, P + A * d, N + q2, 2 if 2 <= d else f)


def walk(k, A, q2, C2, P, N, f, n, D, seen):
    """children that start at entry D, in the order of the Lean list (longest piece first); each with the tuple
    of class names its piece adds"""
    out = []
    added = []
    while n > 0:
        c = canon(k, D)
        if c in seen or c in added:
            break
        added.append(c)
        x = exc(k, D)
        ch = kid(A, q2, C2, P, N, f, n - 1, x)
        if ch is not None:
            out.append((ch, tuple(added)))
        D = doorc(k, x)
        n -= 1
    out.reverse()
    return out


def children(k, A, q2, C2, st, seen):
    y, P, N, f = st
    base = (y % pw(k - 3)) * 4096
    a = y // pw(k - 1)
    b = (y // pw(k - 2)) % 16
    c = (y // pw(k - 3)) % 16
    out = []
    for D in (base + (a * 256 + b * 16 + c), base + (a * 256 + c * 16 + b), base + (b * 256 + a * 16 + c),
              base + (b * 256 + c * 16 + a), base + (c * 256 + a * 16 + b), base + (c * 256 + b * 16 + a)):
        out.extend(walk(k, A, q2, C2, P, N, f, k - 1, D, seen))
    return out


def viol(C1, bn, st):
    y, P, N, f = st
    return f == 2 and not (N + C1 <= P + bn)


def root_children(k, A, q2, C2):
    return walk(k, A, q2, C2, 0, 0, 1, k - 1, idc(k), set())


def params(k, cn, bn, q):
    """(A, q2, C1, C2) for the statement with c = cn/q, b = bn/q"""
    return q * (k - 3) - cn, 2 * q, 2 * q * (k - 4), 2 * q * (k - 3)


def run_search(k):
    """mirror of runSearch: True if one block can be followed by k-2 full pieces"""
    seen = {canon(k, idc(k))}
    count = [0]

    def go(fuel, st):
        count[0] += 1
        if fuel == 0:
            return True
        for ch, added in children(k, 0, 0, 0, st, seen):
            seen.update(added)
            r = go(fuel - 1, ch)
            seen.difference_update(added)
            if r:
                return True
        return False

    return go(k - 2, (exc(k, idc(k)), 0, 0, 0)), count[0]


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(1000000)
    if sys.argv[1] == 'run':
        for k in range(5, 16):
            print(k, run_search(k))
    else:
        k, cn, bn, q = (int(x) for x in sys.argv[1:5])
        A, q2, C1, C2 = params(k, cn, bn, q)
        seen = set()
        stats = dict(states=0, maxdepth=0, found=False)

        def go(st, depth):
            stats['states'] += 1
            stats['maxdepth'] = max(stats['maxdepth'], depth)
            if viol(C1, bn, st):
                stats['found'] = True
                return True
            for ch, added in children(k, A, q2, C2, st, seen):
                seen.update(added)
                r = go(ch, depth + 1)
                seen.difference_update(added)
                if r:
                    return True
            return False

        res = False
        for ch, added in root_children(k, A, q2, C2):
            seen.update(added)
            r = go(ch, 1)
            seen.difference_update(added)
            if r:
                res = True
                break
        print(f"k={k} cn={cn} bn={bn} q={q} A={A} q2={q2} C1={C1} C2={C2}: found={res} states={stats['states']} "
              f"fuel>={stats['maxdepth']}")
