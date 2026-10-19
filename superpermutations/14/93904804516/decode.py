#!/usr/bin/env python3
"""Decode and structurally check an optimized superpermutation group plan.

Uses only the Python standard library. The slice construction is Jay Pantone's;
the bundled seed is Jakub Halfar's.
"""
import argparse
from functools import lru_cache
import hashlib
from itertools import permutations
import json
import lzma
import math
from pathlib import Path
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rotate(b, offset):
    offset %= len(b)
    return b[offset:] + b[:offset]


def insert(b, symbol, position):
    return b[:position] + bytes([symbol]) + b[position:]


def validate_recipe(recipe):
    require(recipe["format"] == "superperm-2lift/1", "Unsupported recipe format.")
    alphabet = recipe["alphabet"].encode("ascii")
    k = len(alphabet) - 4
    require(4 <= k <= 12 and len(set(alphabet)) == len(alphabet)
            and not any(chr(c).isspace() for c in alphabet), "Invalid alphabet.")
    seed = recipe["seed"].encode("ascii")
    require(hashlib.sha256(seed).hexdigest() == recipe["seed_sha256"], "Seed hash mismatch.")
    rows, loops, heads, detached = [], set(), {}, []
    for line in seed.decode("ascii").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        text, kind = line.split()
        b = bytes("0123456789ABCDEF".index(c) for c in text)
        require(sorted(b) == list(range(k)) and kind in ("F", "S", "D"), "Invalid seed row.")
        canonical = rotate(b, b.index(0))
        require(canonical not in loops, "Repeated cyclic seed ordering.")
        loops.add(canonical)
        if kind == "D":
            detached.append(b)
        else:
            require(b[:-2] not in heads, "Repeated live head.")
            heads[b[:-2]] = len(rows)
        rows.append((b, kind))
    require(len(loops) == math.factorial(k - 1), "Incomplete seed.")
    seen, walks = set(), []
    for i, (_, kind) in enumerate(rows):
        if kind == "D" or i in seen:
            continue
        walk, j = [], i
        while j not in seen:
            seen.add(j)
            b, kind = rows[j]
            walk.append((b, kind))
            tail = rotate(b, 1 if kind == "F" else -1)[:-2]
            require(tail in heads, "Unbalanced live walk.")
            j = heads[tail]
        require(j == i and any(t == "F" for _, t in walk), "Invalid closed walk.")
        walks.append(walk)
    require(len(seen) + len(detached) == len(rows), "Unvisited seed rows.")
    short = sum(t == "S" for _, t in rows)
    winding = sum(math.gcd(k - 1, sum(1 if t == "F" else -1 for _, t in w)) for w in walks)
    n = k + 4
    length = (sum(math.factorial(n - i) for i in range(3)) + 2 * short * k * (k + 1)
              + len(detached) * (k * k + 3 * k - 1) + 2 * winding * k * (k + 1))
    require(type(recipe["length"]) is int and recipe["length"] == length, "Length ledger mismatch.")
    return recipe, detached, walks


def transport(walk):
    """Visit port orbits in increasing initial-port order."""
    k = len(walk[0][0])
    done = set()
    for start in range(k - 1):
        if start in done:
            continue
        result, port = [], start
        while True:
            require(port not in done, "Repeated transport port.")
            done.add(port)
            for b, kind in walk:
                if kind == "F":
                    gaps = (0, k - 1) if port == 0 else (port,)
                    result.extend((insert(b, k, j), kind) for j in gaps)
                elif port < k - 2:
                    result.append((insert(b, k, port), kind))
                else:
                    result.extend(((insert(b, k, k - 2), kind),
                                   (rotate(insert(b, k, k - 1), -1), kind)))
                port = (port + (-1 if kind == "F" else 1)) % (k - 1)
            if port == start:
                break
        require(sum(1 if t == "F" else -1 for _, t in result) % k == 0,
                "Transport winding mismatch.")
        yield result


def complete(b, kind, port):
    k = len(b)
    if kind == "F":
        gaps = (0, k - 1) if port == 0 else (port,)
        return [(insert(b, k + 1, j), k, k + 1) for j in gaps]
    if port < k - 2:
        return [(insert(b, k + 1, port), k, k - 1)]
    return [(insert(b, k + 1, k - 2), k, k - 2),
            (rotate(b, k - 2) + bytes([k]), k + 1, k + 1),
            (rotate(b, k - 1) + bytes([k]), k + 1, k + 1),
            (insert(b, k + 1, k - 1), k, k - 2)]


def contribution(b, satellite, visible):
    """A cyclic slice with its shared ending removed."""
    parts = [b, bytes([satellite]), b]
    for i in range(visible - 1):
        parts.extend((bytes([b[i], satellite]), rotate(b, i + 1)))
    return b"".join(parts)[:-(len(b) - 2)]


def small_group(x):
    k = len(x)
    for gap in range(k):
        y = insert(x, k, gap)
        for i in range(k + 1):
            at = (gap + 1 + i) % (k + 1)
            loop = insert(y, k + 1, at)
            cycle = b"".join(contribution(rotate(loop, at + 1 + j) + bytes([k + 2]),
                                           k + 3, k + 3) for j in range(k + 2))
            overlap = (k - 1 if i == 0 else k) if gap or i else 0
            yield (cycle + cycle[:k + 1])[overlap:]


def live_group(walk):
    k = len(walk[0][0])
    h = k - 1
    require(sum(1 if t == "F" else -1 for _, t in walk) % h == 0, "Open completed walk.")
    first = next(i for i, (_, t) in enumerate(walk) if t == "F")
    ordered = walk[first:] + walk[:first]
    for start in range(h):
        parts, port = [], start
        for b, kind in ordered:
            parts.extend(contribution(*s) for s in complete(b, kind, port))
            port = (port + (-1 if kind == "F" else 1)) % h
        require(port == start, "Completion winding mismatch.")
        cycle = b"".join(parts)
        cut = (start + 1) * (k + 3)
        opened = cycle[cut:] + cycle[:cut]
        yield (opened + opened[:h + 1])[h if start else 0:]


def chunks(detached, walks):
    """Reconstruct the unoptimized base word for small-instance comparisons."""
    for x in detached:
        yield from small_group(x)
    for walk in walks:
        for first in transport(walk):
            for second in transport(first):
                yield from live_group(second)


def overlap(a, b):
    for k in range(min(len(a), len(b)), 0, -1):
        if a[-k:] == b[:k]:
            return k
    return 0


def transport_at(walk, start):
    """Select one transport orbit directly; its least initial port is start."""
    k = len(walk[0][0])
    h = k - 1
    count = math.gcd(h, sum(1 if t == 'F' else -1 for _, t in walk))
    require(0 <= start < count, 'Transport orbit out of range.')
    result, port = [], start
    while True:
        for b, kind in walk:
            if kind == 'F':
                gaps = (0, k - 1) if port == 0 else (port,)
                result.extend((insert(b, k, j), kind) for j in gaps)
            elif port < k - 2:
                result.append((insert(b, k, port), kind))
            else:
                result.extend(((insert(b, k, k - 2), kind),
                               (rotate(insert(b, k, k - 1), -1), kind)))
            port = (port + (-1 if kind == 'F' else 1)) % h
        if port == start:
            break
    return result


def resolve_row(walk, row, kind='F'):
    if isinstance(row, str):
        b = bytes.fromhex(row)
        found = next((i for i, (x, t) in enumerate(walk) if x == b and t == kind), None)
        require(found is not None, 'Encoded anchor row absent from walk or has wrong kind.')
        return found
    return row


def phase_info(m, phase):
    require(type(phase) is int, 'Invalid phase.')
    if 120 <= phase < 120+4*(m-1):
        return 0, short_drop_templates(m)[phase-120][2]
    if 100 <= phase:
        rotation = phase-100
        require(0 <= rotation <= m-3 or rotation == m-1, 'Invalid short phase.')
        return rotation, int(rotation not in (0,m-1))
    if phase in (0, 1):
        return phase, 0
    require(3 <= phase <= m + 1, 'Invalid phase.')
    return phase - 2, 1


@lru_cache(maxsize=8)
def short_drop_templates(m):
    """Open a short repair after omitting one of two identical permutation windows."""
    n,h=m+2,m-1;b=bytes(range(m));regular=[]
    for p in range(h-1):
        word=b''.join(contribution(*s) for s in complete(b,'S',p))
        cut=(p+1)*(n+1)
        regular.append((word[cut:cut+n],word[cut-2:cut-2+n],cut,n-2))
    word=b''.join(contribution(*s) for s in complete(b,'S',h-1))
    first=(m-2)*(n+1)+1;third=first+2*n*n
    result=[]
    for cut in (first,first+n+1,third-n-1,third):
        options=regular+[(word[cut:cut+n],word[cut-3:cut-3+n],cut,n-3)]
        for start in range(h):
            ports=list(range(start,h))+list(range(start))
            fee=sum(options[p][3] for p in ports)-sum(min(h,overlap(options[p][1],options[q][0]))
                    for p,q in zip(ports,ports[1:]))-2*h
            result.append((options[ports[0]][0],options[ports[-1]][1],fee,
                           [(p,options[p][2],options[p][3]) for p in ports]))
    return result


@lru_cache(maxsize=8)
def detached_template(k):
    word = b''.join(small_group(bytes(range(k))))
    repeat = k - 1
    require(word[-repeat:] == word[:repeat], 'Detached closure differs.')
    return word[:-repeat]


@lru_cache(maxsize=200000)
def detached_cut(k, at):
    cycle = detached_template(k)
    n = k + 4
    wrapped = cycle + cycle[:n]
    require(type(at) is int and 0 <= at < len(cycle), 'Detached cut out of range.')
    def segment(start, length):
        start %= len(cycle)
        return wrapped[start:start + length]
    head = segment(at, n)
    require(len(set(head)) == n, 'Detached cut is not a permutation window.')
    gap = next(d for d in range(1, n + 1) if len(set(segment(at - d, n))) == n)
    repeat = n - gap
    fee = repeat - (k - 1)
    require(0 <= fee <= 4, 'Unexpected detached opening cost.')
    tail = segment(at - gap, gap) + head[:repeat]
    return head, tail, fee, repeat


def detached_chunks(x, choice):
    at, mode = choice
    if mode == 0:
        yield from small_group(rotate(x, at))
        return
    require(type(mode) is int and 1 <= mode <= 24, 'Invalid detached mode.')
    k = len(x)
    _, _, _, repeat = detached_cut(k, at)
    cycle = detached_template(k)
    opened = cycle[at:] + cycle[:at]
    labels = bytes(list(permutations(range(k,k+4)))[mode-1])
    table = bytes.maketrans(bytes(range(k+4)), x+labels)
    yield (opened + opened[:repeat]).translate(table)


def live_chunks(walk, row, phase):
    """Open every closed trail fully, then overlap consecutive trails by h."""
    m = len(walk[0][0])
    short = phase >= 100
    kind = 'S' if short else 'F'
    row = resolve_row(walk, row, kind)
    h, n = m - 1, m + 2
    require(0 <= row < len(walk) and walk[row][1] == kind, 'Cut row has wrong kind.')
    rotation, fee = phase_info(m, phase)
    drop = phase >= 120
    drop_info = short_drop_templates(m)[phase-120] if drop else None
    ordered = walk[row:] + walk[:row]
    if drop:
        ports=[p for p,_,_ in drop_info[3]]
    elif short and rotation == m-1:
        ports = [h-1]+list(range(h-1))
    elif rotation == m - 1:
        ports = list(range(h))
    else:
        ports = list(range(rotation, h)) + list(range(rotation))
    prev = None
    internal_cost = 0
    for start in ports:
        parts, port = [], start
        for b, kind in ordered:
            parts.extend(contribution(*s) for s in complete(b, kind, port))
            port = (port + (-1 if kind == 'F' else 1)) % h
        require(port == start, 'Completion is not closed.')
        cycle = b''.join(parts)
        if drop:
            _,cut,repeat=next(s for s in drop_info[3] if s[0]==start)
        elif short:
            cut = (m-2)*(n+1)+1+n*n if start == h-1 else (start+1)*(n+1)
        else:
            cut = ((n * n + m * (n + 1)) if (phase == 1 or rotation == m - 1) and start == 0
                   else (start + 1) * (n + 1))
        opened = cycle[cut:] + cycle[:cut]
        if not drop:repeat = h if short and start == h-1 else h+1
        piece = opened + opened[:repeat]
        if prev is not None:
            ov = min(h, overlap(prev, piece[:n]))
            require(ov >= h-(2 if drop else 1), 'Internal trail overlap differs.')
            internal_cost += h - ov
        else:
            ov = 0
        yield piece[ov:]
        prev = piece[-n:]
    require(internal_cost == fee+int(short), 'Internal phase cost differs.')


def ends_and_length(desc, choice, detached, second=None):
    row, phase = choice
    if desc[0] == 0:
        x = detached[desc[1]]
        k = len(x)
        length = k * (k + 1) * (k + 2) * (k + 4) ** 2 + k * k + 3 * k - 1
        if phase == 0:
            require(0 <= row < k, 'Invalid detached rotation.')
            x = rotate(x, row)
            return (x + bytes(range(k, k + 4)),
                    bytes(range(k + 3, k - 1, -1)) + rotate(x, -1), length)
        require(type(phase) is int and 1 <= phase <= 24, 'Invalid detached mode.')
        head, tail, fee, _ = detached_cut(k, row)
        labels = bytes(list(permutations(range(k,k+4)))[phase-1])
        table = bytes.maketrans(bytes(range(k+4)), x+labels)
        return head.translate(table), tail.translate(table), length + fee
    require(second is not None, 'Missing live walk.')
    short = phase >= 100
    kind = 'S' if short else 'F'
    row = resolve_row(second, row, kind)
    require(0 <= row < len(second) and second[row][1] == kind, 'Invalid anchor row.')
    m = len(second[row][0])
    rotation, fee = phase_info(m, phase)
    b = rotate(second[row][0], rotation)
    m = len(b)
    R = m * (m + 2) ** 2 * len(second) + 2 * sum(t == 'S' for _, t in second)
    if phase >= 120:
        head,tail,fee,_=short_drop_templates(m)[phase-120]
        table=bytes.maketrans(bytes(range(m)),b)
        return head.translate(table),tail.translate(table),R+2*(m-1)+fee
    head_pair = [m,m+1] if short and rotation == m-1 else [m+1,m]
    tail_pair = [m+1,m] if short and rotation == 0 else [m,m+1]
    return (b + bytes(head_pair), bytes(tail_pair) + rotate(b, -1 if fee else -2),
            R + 2 * (m - 1) + fee)


def check(plan, detached, walks):
    """Check every group is used exactly once, its endpoints, and the exact ledger."""
    require(plan['format'] == 'superperm-group-plan/1', 'Unknown plan format.')
    entries = {}
    for desc, choice in plan['plan']:
        require(isinstance(desc, list) and len(desc) in (2, 4)
                and all(type(x) is int for x in desc), 'Invalid group.')
        require(desc[0] in (0, 1) and len(desc) == (2 if desc[0] == 0 else 4), 'Invalid group.')
        require(isinstance(choice, list) and len(choice) == 2 and type(choice[1]) is int,
                'Invalid opening choice.')
        require(type(choice[0]) is int or (desc[0] == 1 and isinstance(choice[0], str)),
                'Invalid anchor row or detached cut.')
        key = tuple(desc)
        require(key not in entries, 'Repeated group.')
        entries[key] = choice
    meta = {}
    for i in range(len(detached)):
        desc = (0, i)
        require(desc in entries, 'Missing detached group.')
        meta[desc] = ends_and_length(desc, entries[desc], detached)
    for wi, walk in enumerate(walks):
        for ai, first in enumerate(transport(walk)):
            for bi, second in enumerate(transport(first)):
                desc = (1, wi, ai, bi)
                require(desc in entries, 'Missing live group.')
                meta[desc] = ends_and_length(desc, entries[desc], detached, second)
    require(len(meta) == len(entries), 'Unknown group in plan.')
    n = len(plan['base']['alphabet'])
    fees = sum((phase_info(n - 2, choice[1])[1] if desc[0] == 1 else
                (detached_cut(n - 4, choice[0])[2] if choice[1] else 0))
               for desc, choice in plan['plan'])
    base_length = sum(x[2] for x in meta.values()) - fees
    require(base_length == plan['base']['length'], 'Base ledger mismatch.')
    prev, total, overlaps = b'', 0, 0
    for desc, _ in plan['plan']:
        head, tail, length = meta[tuple(desc)]
        ov = overlap(prev, head)
        overlaps += ov
        total += length - ov
        prev = tail
    require(type(plan['length']) is int and plan['length'] == total, 'Plan ledger mismatch.')
    return {'n': len(plan['base']['alphabet']), 'length': total,
            'base_length': base_length, 'saving': overlaps - fees,
            'overlaps': overlaps, 'phase_cost': fees, 'groups': len(meta),
            'seed_checked': True, 'group_partition_checked': True,
            'verification': 'structural; no full word scan'}


def word_chunks(plan, detached, walks):
    @lru_cache(maxsize=16)
    def first_walk(wi, ai):
        return transport_at(walks[wi], ai)

    prev = b''
    for desc, choice in plan['plan']:
        if desc[0] == 0:
            source = detached_chunks(detached[desc[1]], choice)
            head, tail, length = ends_and_length(desc, choice, detached)
        else:
            _, wi, ai, bi = desc
            second = transport_at(first_walk(wi, ai), bi)
            source = live_chunks(second, *choice)
            head, tail, length = ends_and_length(desc, choice, detached, second)
        ov = overlap(prev, head)
        first = True
        actual_tail = b''
        actual_length = 0
        for chunk in source:
            if first:
                require(chunk[:len(head)] == head, 'Actual group head differs.')
                chunk = chunk[ov:]
                first = False
            actual_tail = (actual_tail + chunk)[-len(tail):]
            actual_length += len(chunk)
            yield chunk
        require(actual_length == length - ov, 'Actual group length differs.')
        require(actual_tail == tail, 'Actual group tail differs.')
        prev = tail


def write_word(plan, detached, walks, output, limit=None):
    """Write a prefix, or exhaust the complete stream and check its exact length."""
    target = plan['length'] if limit is None else limit
    require(type(target) is int and 0 <= target <= plan['length'], 'Invalid output limit.')
    complete = target == plan['length']
    table = bytes.maketrans(bytes(range(len(plan['base']['alphabet']))),
                            plan['base']['alphabet'].encode('ascii'))
    digest, count = hashlib.sha256(), 0
    if target:
        for chunk in word_chunks(plan, detached, walks):
            data = (chunk if complete else chunk[:target - count]).translate(table)
            require(count + len(data) <= target, 'Decoded output exceeds the expected length.')
            output.write(data)
            digest.update(data)
            count += len(data)
            if not complete and count == target:
                break
    require(count == target, 'Decoded length mismatch.')
    return {'symbols': count, 'complete': complete, 'sha256': digest.hexdigest()}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('recipe', type=Path)
    p.add_argument('output', nargs='?', help='New output file, or - for stdout.')
    p.add_argument('--check-recipe', action='store_true',
                   help='Validate the seed, group partition, and length without expanding the word.')
    p.add_argument('--limit', type=int, help='Write only this many initial symbols.')
    args = p.parse_args()
    try:
        with lzma.open(args.recipe, 'rt', encoding='ascii') as f:
            plan = json.load(f)
        if args.check_recipe:
            require(args.output is None and args.limit is None, 'Check takes no output or limit.')
        else:
            require(args.output is not None, 'Specify output or --check-recipe.')
            require(args.limit is None or 0 <= args.limit <= plan['length'], 'Invalid output limit.')
        _, detached, walks = validate_recipe(plan['base'])
        report = check(plan, detached, walks)
        if not args.check_recipe:
            if args.output == '-':
                report = write_word(plan, detached, walks, sys.stdout.buffer, args.limit)
                sys.stdout.buffer.flush()
            else:
                with open(args.output, 'xb', buffering=8 << 20) as out:
                    report = write_word(plan, detached, walks, out, args.limit)
        print(json.dumps(report), file=sys.stderr)
    except (ValueError, TypeError, KeyError, IndexError, OSError, lzma.LZMAError) as error:
        p.exit(1, f'decode: {error}\n')


if __name__ == '__main__':
    main()
