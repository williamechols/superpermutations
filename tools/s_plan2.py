"""Cut the search `S.search k A q2 C1 C2 bn fuel` (LowerBounds/SSearch.lean) into parts that the Lean kernel can
evaluate one at a time, with the state of every plan node written out.

Same plan as s_plan.py.  The difference: in s_plan.py the state of a plan node is `stepPath` from the state after
the first piece, so every lemma about a node at depth D first evaluates D states.  Here the state of every plan
node is a literal (exit, tree of used classes, scores, flag: `X_lit`), and one more lemma per node,

    X_eq :  St.beq (stepPath ... PARENT_lit path) X_lit = true          (by decide +kernel; `a` states)

says that the literal is the state the path leads to (`S.ref_of_lit`, SLit.lean).  So no lemma depends on the depth
of its node.  The literals come from the Python mirror (s_ksim.py and the tree insertion below); nothing computed
here is trusted by Lean: a wrong literal or a wrong plan makes a lemma fail.

usage: s_plan2.py k cn bn q NAME [--fuel F] [--leaf N] [--band N] [--per-file N] [--maxh H] [--dry]
  writes LowerBounds/SGen/<NAME>D<i>.lean (states and path lists), <NAME>Defs.lean (imports them), <NAME>P<i>.lean (the
  lemmas), <NAME>.lean (the assembly) and s_gen_<NAME>.txt (module names in build order, in stages separated by
  "--"; the modules of a stage are independent of each other).
"""
import sys, os, argparse
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import s_ksim as ks
sys.setrecursionlimit(1000000)

ap = argparse.ArgumentParser()
ap.add_argument("k", type=int); ap.add_argument("cn", type=int); ap.add_argument("bn", type=int)
ap.add_argument("q", type=int); ap.add_argument("name")
ap.add_argument("--fuel", type=int, default=0, help="fuel of the search (default: deepest prefix in pieces)")
ap.add_argument("--leaf", type=int, default=1000, help="largest number of states evaluated by one lemma")
ap.add_argument("--band", type=int, default=500, help="largest number of states expanded by one cover lemma")
ap.add_argument("--per-file", type=int, default=6000, help="states per generated file (approximate)")
ap.add_argument("--maxh", type=int, default=150, help="largest height of a subtree checked by one lemma")
ap.add_argument("--chunk", type=int, default=400000, help="characters of written-out states per file")
ap.add_argument("--plain", action="store_true", help="write the trees as terms Tr.node ..., not as packed lists")
ap.add_argument("--dry", action="store_true", help="print the plan only")
args = ap.parse_args()
K, CN, BN, Q, NAME = args.k, args.cn, args.bn, args.q, args.name
A, Q2, C1, C2 = ks.params(K, CN, BN, Q)

# ---------------------------------------------------------------- the tree of the search (structure only)
class Node:
    __slots__ = ("kids", "size", "h")
    def __init__(self): self.kids = []; self.size = 1; self.h = 1

seen = set()
def build(st):
    n = Node()
    if ks.viol(C1, BN, st):
        raise SystemExit("the search returns true (a violating window is found); nothing to prove")
    for ch, added in ks.children(K, A, Q2, C2, st, seen):
        seen.update(added)
        kd = build(ch)
        seen.difference_update(added)
        n.kids.append(kd); n.size += kd.size
        if kd.h + 1 > n.h: n.h = kd.h + 1
    return n

roots = []
for ch, added in ks.root_children(K, A, Q2, C2):
    seen.update(added)
    roots.append(build(ch))
    seen.difference_update(added)
total = sum(r.size for r in roots)
height = max(r.h for r in roots)
FUEL = args.fuel if args.fuel else height
if FUEL < height:
    raise SystemExit(f"fuel {FUEL} is less than the deepest prefix {height}")
print(f"search {K} {A} {Q2} {C1} {C2} {BN} {FUEL}: {len(roots)} states after the first piece, {total} calls of goK, "
      f"deepest prefix {height} pieces")

def level(node, a):
    """paths (lists of child indices) of the nodes at depth a below node, with the nodes, in search order"""
    out = []
    def go(n, d, path):
        if d == a:
            out.append((list(path), n)); return
        for i, kd in enumerate(n.kids):
            path.append(i); go(kd, d + 1, path); path.pop()
    go(node, 0, [])
    return out

def band(node, a, cap):
    """number of states at depth < a below node (the states a cover lemma expands), stopped above cap"""
    cnt = 0
    stack = [(node, 0)]
    while stack:
        n, d = stack.pop()
        if d >= a: continue
        cnt += 1
        if cnt > cap: return cnt
        for kd in n.kids: stack.append((kd, d + 1))
    return cnt

# ---------------------------------------------------------------- states written out
def ins(t, x):
    """mirror of Tr.ins: a tree is None or (left, key, right)"""
    if t is None: return (None, x, None)
    l, key, r = t
    if key <= x: return (l, key, ins(r, x))
    return (ins(l, x), key, r)

def keys(t, out):
    stack = [t]
    while stack:
        n = stack.pop()
        if n is None: continue
        out.add(n[1]); stack.append(n[0]); stack.append(n[2])
    return out

def walk_to(state, path):
    """the state (st, tree) reached from `state` by taking child path[0], path[1], ..."""
    st, T = state
    sn = keys(T, set())
    for i in path:
        ch, added = ks.children(K, A, Q2, C2, st, sn)[i]
        for c in added: T = ins(T, c)
        sn.update(added); st = ch
    return (st, T)

def lit_tree(t):
    if t is None: return "Tr.leaf"
    return f"(Tr.node {lit_tree(t[0])} {t[1]} {lit_tree(t[2])})"

RECB = 2 ** 68
def height(t):
    """height of a tree, without recursion on the Python stack beyond the height itself"""
    if t is None: return 0
    return 1 + max(height(t[0]), height(t[2]))

def packed_tree(t):
    """the tree in preorder as records 4*key + 2*hasRight + hasLeft, 32 records per number (mirror of SDec.lean)"""
    recs = []
    stack = [t]
    while stack:
        n = stack.pop()
        l, key, r = n
        recs.append(4 * key + 2 * (r is not None) + (l is not None))
        if r is not None: stack.append(r)
        if l is not None: stack.append(l)
    out = []
    for i in range(0, len(recs), 32):
        v = 0
        for j, rc in enumerate(recs[i:i + 32]):
            v += rc * RECB ** j
        out.append(v)
    return out

def lit_state(state):
    (y, P, N, f), T = state
    if args.plain:
        return f"⟨{y},\n    {lit_tree(T)},\n    {P}, {N}, {f}⟩"
    if T is None:
        return f"⟨{y}, Tr.leaf, {P}, {N}, {f}⟩"
    nums = packed_tree(T)
    body = ",\n     ".join(str(v) for v in nums)
    return f"⟨{y},\n    trOf {height(T) + 1}\n    [{body}],\n    {P}, {N}, {f}⟩"

# ---------------------------------------------------------------- the plan
class Plan:
    def __init__(self, ident, fuel, node, parent, path, state):
        self.id = ident; self.fuel = fuel; self.node = node; self.parent = parent; self.path = path
        self.state = state
        self.a = None; self.groups = []     # groups: ("leafgroup", [paths], states) or ("child", path, Plan)

plans = []          # all plan nodes, parents before children
lemmas = []         # (kind, plan, group index, cost)

def small(node):
    return node.size <= args.leaf and node.h <= args.maxh

def make(ident, fuel, node, parent, path, state):
    P = Plan(ident, fuel, node, parent, path, state)
    plans.append(P)
    lemmas.append(("eq", P, None, len(path) if path is not None else 1))
    if small(node):
        P.a = 0
        lemmas.append(("leaf", P, None, node.size))
        return P
    h = node.h
    amax = 1
    for a in range(1, min(h, args.maxh + 1)):
        if band(node, a, args.band) > args.band: break
        amax = a
    cands = range(max(1, amax - 4), amax + 1)
    best = min(cands, key=lambda a: (len(level(node, a)), -a))
    lv = level(node, best)
    if lv and max(n.size for _, n in lv) >= node.size - 1 and best < amax:
        best = amax; lv = level(node, best)
    P.a = best
    lemmas.append(("cover", P, None, band(node, best, 10 ** 9)))
    cur, cur_size = [], 0
    def flush():
        nonlocal cur, cur_size
        if cur:
            P.groups.append(("leafgroup", cur, cur_size))
            lemmas.append(("group", P, len(P.groups) - 1, cur_size))
            cur, cur_size = [], 0
    for pth, n in lv:
        if not small(n):
            flush()
            gi = len(P.groups)
            P.groups.append(None)
            child = make(f"{ident}_{gi}", fuel - best, n, P, pth, walk_to(state, pth))
            P.groups[gi] = ("child", pth, child)
        else:
            # a group lemma walks to the end of each path (`best` states) and then searches below it
            if cur and cur_size + n.size + best > args.leaf: flush()
            cur.append(pth); cur_size += n.size + best
    flush()
    return P

tops = []
for i, (r, (ch, added)) in enumerate(zip(roots, ks.root_children(K, A, Q2, C2))):
    T = None
    for c in added: T = ins(T, c)
    tops.append(make(f"r{i}", FUEL, r, None, None, (ch, T)))
print(f"plan: {len(plans)} plan nodes, {len(lemmas)} lemmas for the kernel;",
      f"largest lemma about {max(l[3] for l in lemmas)} states; total {sum(l[3] for l in lemmas)} states")
if args.dry:
    sys.exit(0)

# ---------------------------------------------------------------- Lean
def lst(xs): return "[" + ", ".join(str(x) for x in xs) + "]"
def rp(path): return lst(list(reversed(path)))            # paths are stored last step first
P4 = f"{K} {A} {Q2} {C2}"
P6 = f"{K} {A} {Q2} {C1} {C2} {BN}"
NS = NAME
D0 = "⟨0, Tr.leaf, 0, 0, 0⟩"
D0S = "⟨0, S.Tr.leaf, 0, 0, 0⟩"
HEAD = f"s_plan2.py {K} {CN} {BN} {Q} {NAME} (fuel {FUEL}, leaf {args.leaf}, band {args.band}, maxh {args.maxh})"

def lit(P): return f"{P.id}_lit"
def origin(P):
    """the expression whose value the literal of P is"""
    if P.parent is None:
        return f"(nthD (rootChildren {P4}) {tops.index(P)} {D0})"
    return f"(stepPath {P4} {lit(P.parent)} ({rp(P.path)} : List Nat).reverse)"

DEFHEAD = f"""/-
Generated by {HEAD}.  Do not edit.
%s
Nothing here is trusted: the lemmas of the files {NS}P*.lean are checked by the kernel.
-/
%s
namespace SuperpermLowerBounds
namespace SGen
namespace {NS}
open S
set_option maxRecDepth 100000
"""
DEFTAIL = f"end {NS}\nend SGen\nend SuperpermLowerBounds\n"
# All definitions of a plan node (its state written out, its path lists, its cover) go to one of the files
# <NAME>D<i>.lean, about `--chunk` characters each; a character of a path list counts five times, because lists of
# lists of numbers cost Lean much more memory to elaborate than a tree.
chunks, curc, curn = [], [], 0
for P in plans:
    ts = [f"{'def' if args.plain else 'noncomputable def'} {lit(P)} : St :=\n  {lit_state(P.state)}\n"]
    w = len(ts[0])
    for gi, g in enumerate(P.groups):
        if g[0] == "leafgroup":
            t = f"def {P.id}_g{gi} : List (List Nat) :=\n  [" + ",\n   ".join(rp(p) for p in g[1]) + "]\n"
        else:
            t = f"def {P.id}_g{gi} : List (List Nat) := [{rp(g[1])}]\n"
        ts.append(t); w += 5 * len(t)
    if P.a:
        if P.groups:
            cover = " ++ (".join(f"{P.id}_g{gi}" for gi in range(len(P.groups))) + " ++ []" + ")" * (len(P.groups) - 1)
        else:
            cover = "[]"
        ts.append(f"def {P.id}_cover : List (List Nat) := {cover}\n")
    if curc and curn + w > args.chunk:
        chunks.append(curc); curc, curn = [], 0
    curc.extend(ts); curn += w
if curc: chunks.append(curc)
cdig = max(2, len(str(len(chunks) - 1)))
cnames = [f"{NS}D{i:0{cdig}d}" for i in range(len(chunks))]
defs = [f"""/-
Generated by {HEAD}.  Do not edit.
The definitions of the plan that cuts `S.search {P6} {FUEL}` into parts are in the files
{cnames[0]} … {cnames[-1]}; this file only imports them.
-/
""" + "".join(f"import LowerBounds.SGen.{c}\n" for c in cnames)]

def lemma_text(kind, P, gi):
    T = "(fun _ _ => true)"
    if kind == "eq":
        return (f"theorem {P.id}_eq : St.beq {origin(P)}\n    {lit(P)} = true := by\n  decide +kernel\n")
    if kind == "leaf":
        return (f"theorem {P.id}_ref : Ref {P6} {P.fuel} {lit(P)} := by\n"
                f"  show goK {P6} {T} {P.fuel} {lit(P)} [] = false\n  decide +kernel\n")
    if kind == "cover":
        return (f"theorem {P.id}_cov : goK {P6} (leafCover {P.id}_cover) {P.a} {lit(P)} [] = false := by\n"
                f"  decide +kernel\n")
    b = P.fuel - P.a
    return (f"theorem {P.id}_g{gi}_ok : ({P.id}_g{gi}).all (fun rp =>\n"
            f"    !goK {P6} {T} {b} (stepPath {P4} {lit(P)} rp.reverse) []) = true := by\n"
            f"  decide +kernel\n")

files, cur, cur_cost = [], [], 0
for (kind, P, gi, cost) in lemmas:
    if cur and cur_cost + cost > args.per_file:
        files.append(cur); cur, cur_cost = [], 0
    cur.append((kind, P, gi, cost)); cur_cost += cost
if cur: files.append(cur)

outdir = os.path.join(HERE, "LowerBounds", "SGen")
os.makedirs(outdir, exist_ok=True)
def write(name, text):
    with open(os.path.join(outdir, name), "w", encoding="utf-8", newline="\n") as f: f.write(text)

for cn_, ch in zip(cnames, chunks):
    write(f"{cn_}.lean", "\n".join([DEFHEAD % (f"States (written out) and path lists of the plan that cuts `S.search {P6} {FUEL}` into parts.",
                                               "import LowerBounds.SSearch\n" if args.plain else "import LowerBounds.SDec\n")] + ch + [DEFTAIL]))
write(f"{NS}Defs.lean", "\n".join(defs))
mods = [f"{NS}Defs"]
ndig = max(2, len(str(len(files) - 1)))
for i, fl in enumerate(files):
    body = [f"""/-
Generated by {HEAD}.  Do not edit.
Part {i + 1} of {len(files)} of the kernel evaluation of `S.search {P6} {FUEL}` (about {sum(l[3] for l in fl)} states).
-/
import LowerBounds.SLit
import LowerBounds.SGen.{NS}Defs

namespace SuperpermLowerBounds
namespace SGen
namespace {NS}
open S
set_option maxRecDepth 100000
"""]
    for (kind, P, gi, cost) in fl:
        body.append(f"-- about {cost} states\n" + lemma_text(kind, P, gi))
    body.append(f"end {NS}\nend SGen\nend SuperpermLowerBounds\n")
    pn = f"{NS}P{i:0{ndig}d}"
    write(f"{pn}.lean", "\n".join(body))
    mods.append(pn)

# assembly
asm = [f"""/-
Generated by {HEAD}.  Do not edit.
`S.search {P6} {FUEL} = false`, put together from the parts {mods[1]} … {mods[-1]} with `S.ref_of_cover`,
`S.ref_of_lit` and `S.search_false`.
-/
import LowerBounds.SCut
import LowerBounds.SLit
""" + "".join(f"import LowerBounds.SGen.{m}\n" for m in mods[1:]) + f"""
namespace SuperpermLowerBounds
namespace SGen
namespace {NS}
open S
set_option maxRecDepth 100000
"""]
for P in reversed(plans):               # children before parents
    if P.a == 0: continue               # leaf: its lemma is `{id}_ref`
    b = P.fuel - P.a
    terms = []
    for gi, g in enumerate(P.groups):
        if g[0] == "leafgroup":
            terms.append(f"(refs_of_all {P6} {b} {lit(P)} {P.id}_g{gi} {P.id}_g{gi}_ok)")
        else:
            terms.append(f"(forall_cons (P := fun rp => Ref {P6} {b} (stepPath {P4} {lit(P)} rp.reverse))\n"
                         f"      (ref_of_lit {g[2].id}_eq {g[2].id}_ref) forall_nil)")
    proof = "forall_nil"
    for t in reversed(terms):
        proof = f"(forall_append {t}\n    {proof})"
    asm.append(f"theorem {P.id}_ref : Ref {P6} {P.fuel} {lit(P)} :=\n"
               f"  ref_of_cover {P6} {P.a} {b} {lit(P)} {P.id}_cover {P.id}_cov\n    {proof}\n")
allp = "S.forall_lt_zero"
PP = f"(P := fun i => S.Ref {P6} {FUEL} (S.nthD (S.rootChildren {P4}) i {D0S}))"
for P in tops:
    allp = f"(S.forall_lt_succ {PP}\n      {allp} (S.ref_of_lit {NS}.{P.id}_eq {NS}.{P.id}_ref))"
asm.append(f"""theorem rootChildren_length : (rootChildren {P4}).length = {len(tops)} := by decide +kernel

end {NS}

/-- The search on numbers finds nothing: evaluated by the kernel in {len(lemmas)} parts. -/
theorem search_{NS} : S.search {P6} {FUEL} = false :=
  S.search_false {P6} {FUEL} {len(tops)} {D0S} {NS}.rootChildren_length
    {allp}

end SGen
end SuperpermLowerBounds
""")
write(f"{NS}.lean", "\n".join(asm))
mods.append(NS)
# build order: stages separated by "--"; the modules of a stage are independent of each other
with open(os.path.join(HERE, f"s_gen_{NAME}.txt"), "w", newline="\n") as f:
    f.write("\n".join(cnames + ["--", mods[0], "--"] + mods[1:-1] + ["--", mods[-1]]) + "\n")
dsize = sum(os.path.getsize(os.path.join(outdir, f"{c}.lean")) for c in cnames)
print(f"wrote {len(files)} part files, {len(cnames)} files of definitions ({dsize // 1024} KB), {NS}Defs.lean, {NS}.lean; "
      f"modules in s_gen_{NAME}.txt")
for i, fl in enumerate(files):
    print(f"  {mods[1 + i]}: {len(fl)} lemmas, about {sum(l[3] for l in fl)} states")
