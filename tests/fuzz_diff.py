#!/usr/bin/env python3
"""Differential mutation fuzzing: corrupt a lean4export file at random and compare the verdicts of
Lean's kernel (the arena's official checker) and lazylean.  A disagreement where lazylean accepts
what the kernel rejects is a soundness bug; the converse a completeness bug.
Usage: fuzz_diff.py export.ndjson N [seed]      (results in ~/ll-tmp/fuzz/)"""
import json, random, subprocess, sys, os, hashlib
SRC, N = sys.argv[1], int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
OFF = os.path.expanduser(os.environ.get("FUZZ_OFFICIAL", "~/dev/lean-kernel-arena/checkers/official/.lake/build/bin/kernel"))
LL = os.path.expanduser(os.environ.get("FUZZ_LAZYLEAN", os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "build", "lazylean")))
OUT = os.path.expanduser(os.environ.get("FUZZ_OUT", "~/ll-tmp/fuzz")); os.makedirs(OUT, exist_ok=True)
lines = open(SRC).read().splitlines()
recs = [json.loads(l) for l in lines]
exprs = [i for i, r in enumerate(recs) if "ie" in r]
levels = [i for i, r in enumerate(recs) if "il" in r]
decls = [i for i, r in enumerate(recs) if not ("ie" in r or "il" in r or "in" in r or "meta" in r)]
def max_idx(key): return max((r[key] for r in recs if key in r), default=0)
nexpr, nlvl = max_idx("ie"), max_idx("il")
def rand_expr_before(i):   # an expression index defined before line i (exports are forward references only)
    cands = [recs[j]["ie"] for j in exprs if j < i]
    return random.choice(cands) if cands else 0
def mutate(rng):
    random.seed(rng)
    kind = random.choice(["decl-value", "decl-type", "expr-child", "level", "natval", "rule-rhs", "ctor-swap", "nparams", "expr-kind", "lparam-drop",
                          "rec-nfields", "rec-k", "rec-counts", "ctor-nfields", "safety", "hint", "lparam-rename", "const-levels", "ind-flags", "rule-drop", "lparam-dup", "ctor-induct"])
    i = None
    if kind in ("decl-value", "decl-type", "rule-rhs", "ctor-swap", "nparams", "lparam-drop", "rec-nfields", "rec-k", "rec-counts", "ctor-nfields", "safety", "hint", "lparam-rename", "ind-flags", "rule-drop", "lparam-dup", "ctor-induct"):
        i = random.choice(decls); r = json.loads(json.dumps(recs[i]))
        k = next(k for k in ("def", "thm", "opaque", "axiom", "quot", "inductive") if k in r)
        if kind == "decl-value" and k in ("def", "thm", "opaque"): r[k]["value"] = rand_expr_before(i)
        elif kind == "decl-type" and k != "inductive": r[k]["type"] = rand_expr_before(i)
        elif kind == "rule-rhs" and k == "inductive" and r[k]["recs"] and r[k]["recs"][0]["rules"]:
            rule = random.choice(r[k]["recs"][0]["rules"]); rule["rhs"] = rand_expr_before(i)
        elif kind == "ctor-swap" and k == "inductive" and len(r[k]["types"][0]["ctors"]) >= 2:
            c = r[k]["types"][0]["ctors"]; a, b = random.sample(range(len(c)), 2); c[a], c[b] = c[b], c[a]
        elif kind == "nparams" and k == "inductive":
            t = r[k]["types"][0]; t["numParams"] = max(0, t["numParams"] + random.choice([-1, 1]))
        elif kind == "lparam-drop" and k != "inductive" and r[k]["levelParams"]: r[k]["levelParams"].pop()
        elif kind == "lparam-rename" and k != "inductive" and r[k]["levelParams"]: r[k]["levelParams"][0] = r[k]["levelParams"][0] + 1
        elif kind == "lparam-dup" and k != "inductive" and r[k]["levelParams"]: r[k]["levelParams"].append(r[k]["levelParams"][0])
        elif kind == "lparam-dup" and k == "inductive" and r[k]["types"][0]["levelParams"]: r[k]["types"][0]["levelParams"].append(r[k]["types"][0]["levelParams"][0])
        elif kind == "ctor-induct" and k == "inductive" and r[k]["ctors"]: r[k]["ctors"][0]["induct"] = random.choice([j for j in range(1, 40)])
        elif kind == "rec-nfields" and k == "inductive" and r[k]["recs"] and r[k]["recs"][0]["rules"]:
            rule = random.choice(r[k]["recs"][0]["rules"]); rule["nfields"] = max(0, rule["nfields"] + random.choice([-1, 1]))
        elif kind == "rec-k" and k == "inductive" and r[k]["recs"]: r[k]["recs"][0]["k"] = not r[k]["recs"][0]["k"]
        elif kind == "rec-counts" and k == "inductive" and r[k]["recs"]:
            rc = r[k]["recs"][0]; fld = random.choice(["numParams", "numIndices", "numMotives", "numMinors"]); rc[fld] = max(0, rc[fld] + random.choice([-1, 1]))
        elif kind == "ctor-nfields" and k == "inductive" and r[k]["ctors"]:
            c = random.choice(r[k]["ctors"]); c["numFields"] = max(0, c["numFields"] + random.choice([-1, 1]))
        elif kind == "safety" and k == "def": r[k]["safety"] = random.choice(["safe", "unsafe", "partial"])
        elif kind == "safety" and k in ("axiom", "opaque"): r[k]["isUnsafe"] = not r[k]["isUnsafe"]
        elif kind == "hint" and k == "def": r[k]["hints"] = random.choice(["opaque", "abbrev", {"regular": random.randint(0, 50)}])
        elif kind == "ind-flags" and k == "inductive":
            t = r[k]["types"][0]; fld = random.choice(["isRec", "isReflexive", "isUnsafe", "numIndices", "numNested"])
            t[fld] = (not t[fld]) if isinstance(t[fld], bool) else max(0, t[fld] + random.choice([-1, 1]))
        elif kind == "rule-drop" and k == "inductive" and r[k]["recs"] and len(r[k]["recs"][0]["rules"]) >= 1:
            r[k]["recs"][0]["rules"].pop(random.randrange(len(r[k]["recs"][0]["rules"])))
        else: return None
        return kind, i, r
    if kind in ("expr-child", "expr-kind", "natval", "const-levels"):
        i = random.choice(exprs); r = json.loads(json.dumps(recs[i]))
        if kind == "natval" and "natVal" in r: r["natVal"] = str(int(r["natVal"]) + random.choice([-1, 1, 7]) if int(r["natVal"]) > 0 else 1)
        elif kind == "expr-child":
            for key in ("app", "lam", "forallE", "letE", "proj", "mdata"):
                if key in r:
                    fields = [f for f in ("fn", "arg", "type", "body", "value", "struct", "expr") if f in r[key] and isinstance(r[key][f], int)]
                    if not fields: return None
                    r[key][random.choice(fields)] = rand_expr_before(i); return kind, i, r
            return None
        elif kind == "expr-kind" and "bvar" in r: r["bvar"] = r["bvar"] + 1
        elif kind == "const-levels" and "const" in r:
            us = r["const"]["us"]
            if us and random.random() < 0.5: us.pop()
            else: us.append(random.choice([j for j in range(nlvl + 1)]) if nlvl else 0)
        else: return None
        return kind, i, r
    if kind == "level":
        i = random.choice(levels); r = json.loads(json.dumps(recs[i]))
        if "succ" in r: r = {"il": r["il"], "max": [r["succ"], r["succ"]]} if random.random() < 0.5 else {"il": r["il"], "succ": 0}
        elif "max" in r: r["max"] = [r["max"][1], r["max"][0]] if random.random() < 0.5 else [r["max"][0], 0]
        elif "imax" in r: r["max"] = r.pop("imax")
        else: return None
        return kind, i, r
def run(bin, path):
    try:
        pre = [] if os.environ.get("FUZZ_NOCAP") else ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=3G", "-p", "MemorySwapMax=0"]
        p = subprocess.run(pre + ["timeout", "120", bin, path], capture_output=True, text=True)
    except Exception as e: return "error", str(e)
    rc = p.returncode
    return ("accept" if rc == 0 else "reject" if rc == 1 else "declined" if rc == 2 else "timeout" if rc == 124 else "error"), (p.stderr.strip().splitlines() or [""])[-1][:200]
stats = {}; disagreements = []
for n in range(N):
    m = mutate(seed * 100003 + n)
    if not m: continue
    kind, i, r = m
    path = os.path.join(OUT, f"mut_{os.getpid()}.ndjson")   # per process: batches may run concurrently
    with open(path, "w") as f:
        for j, l in enumerate(lines): f.write((json.dumps(r, separators=(",", ":")) if j == i else l) + "\n")
    o, omsg = run(OFF, path); l, lmsg = run(LL, path)
    key = (kind, o, l); stats[key] = stats.get(key, 0) + 1
    agree = (o == l) or (o in ("reject", "error") and l == "reject")   # a lazylean crash/timeout is always reported
    if not agree:
        keep = os.path.join(OUT, f"disagree_{os.path.basename(SRC)}_{seed}_{n}_{kind}_{o}_{l}.ndjson"); os.replace(path, keep)
        disagreements.append((n, kind, o, l, omsg, lmsg, keep))
        print(f"DISAGREE #{n} {kind}: official={o} lazylean={l}\n   official: {omsg}\n   lazylean: {lmsg}\n   {keep}", flush=True)
    elif n % 25 == 0: print(f"  {n}: {kind} -> {o}/{l}", flush=True)
print("\nsummary (mutation, official, lazylean): count")
for k, v in sorted(stats.items()): print(f"  {k}: {v}")
print(f"{len(disagreements)} disagreements")
