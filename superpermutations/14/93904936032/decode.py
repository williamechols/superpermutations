#!/usr/bin/env python3
"""Decode recipe using only the Python standard library.

The slice construction is Jay Pantone's; the bundled seed is Jakub Halfar's.
"""
import argparse
import hashlib
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


def read_recipe(path):
    with lzma.open(path, "rt", encoding="ascii") as stream:
        recipe = json.load(stream)
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
    for x in detached:
        yield from small_group(x)
    for walk in walks:
        for first in transport(walk):
            for second in transport(first):
                yield from live_group(second)


def write_word(recipe, detached, walks, output, limit=None):
    target = recipe["length"] if limit is None else limit
    require(0 <= target <= recipe["length"], "Limit must be between zero and the full length.")
    table = bytes.maketrans(bytes(range(len(recipe["alphabet"]))), recipe["alphabet"].encode("ascii"))
    digest, count = hashlib.sha256(), 0
    if target:
        for chunk in chunks(detached, walks):
            data = (chunk if limit is None else chunk[:target - count]).translate(table)
            require(count + len(data) <= target, "Decoded output exceeds the expected length.")
            output.write(data)
            digest.update(data)
            count += len(data)
            if limit is not None and count == target:
                break
    require(count == target, "Decoded length mismatch.")
    return {"symbols": count, "complete": count == recipe["length"], "sha256": digest.hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("recipe", type=Path)
    parser.add_argument("output", nargs="?", help="New output file, or - for stdout.")
    parser.add_argument("--check-recipe", action="store_true", help="Validate the seed and length ledger without expanding the word.")
    parser.add_argument("--limit", type=int, help="Write only this many initial symbols.")
    args = parser.parse_args()
    try:
        recipe, detached, walks = read_recipe(args.recipe)
        if args.check_recipe:
            require(args.output is None and args.limit is None, "--check-recipe takes no output or limit.")
            report = {"format": recipe["format"], "n": len(recipe["alphabet"]),
                      "alphabet": recipe["alphabet"], "length": recipe["length"],
                      "seed_checked": True, "detached": len(detached), "walks": len(walks)}
        else:
            require(args.output is not None, "Specify an output file, - for stdout, or --check-recipe.")
            require(args.limit is None or 0 <= args.limit <= recipe["length"], "Invalid limit.")
            if args.output == "-":
                report = write_word(recipe, detached, walks, sys.stdout.buffer, args.limit)
                sys.stdout.buffer.flush()
            else:
                with open(args.output, "xb", buffering=8 << 20) as output:
                    report = write_word(recipe, detached, walks, output, args.limit)
        print(json.dumps(report), file=sys.stderr)
    except (ValueError, KeyError, TypeError, OSError, lzma.LZMAError) as error:
        parser.exit(1, f"decode: {error}\n")


if __name__ == "__main__":
    main()
