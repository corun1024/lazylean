#!/usr/bin/env python3
"""Append to a lean4export file the theorem  name : (d : Bool) = true := Eq.refl true  for each given
Bool-valued constant d (no elaborator involved: the kernel alone evaluates d).
Usage: synth_decide.py in.ndjson out.ndjson decl [decl ...]"""
import json, sys
src, dst, decls = sys.argv[1], sys.argv[2], sys.argv[3:]
lines = open(src).read().splitlines()
names = {0: ""}; name_of = {"": 0}; nexpr = -1; nlvl = 0; nname = 0
lvl1 = None   # index of level `1` (succ zero), if present
lvl_of = {}
consts = {}   # (name idx, us tuple) -> expr idx
for l in lines:
    o = json.loads(l)
    if "in" in o:
        i = o["in"]; nname = max(nname, i)
        if "str" in o: names[i] = (names[o["str"]["pre"]] + "." + o["str"]["str"]).lstrip(".")
        else: names[i] = names[o["num"]["pre"]] + "." + str(o["num"]["i"])
        name_of[names[i]] = i
    elif "il" in o:
        nlvl = max(nlvl, o["il"])
        if "succ" in o and o["succ"] == 0: lvl1 = o["il"]
    elif "ie" in o:
        nexpr = max(nexpr, o["ie"])
        if "const" in o: consts[(o["const"]["name"], tuple(o["const"]["us"]))] = o["ie"]
out = list(lines)
def add_name(s):
    global nname
    if s in name_of: return name_of[s]
    pre, _, last = s.rpartition(".")
    p = add_name(pre) if pre else 0
    nname += 1; out.append(json.dumps({"in": nname, "str": {"pre": p, "str": last}}, separators=(",", ":")))
    names[nname] = s; name_of[s] = nname; return nname
if lvl1 is None:
    nlvl += 1; out.append(json.dumps({"il": nlvl, "succ": 0}, separators=(",", ":"))); lvl1 = nlvl
def add_expr(rec):
    global nexpr
    nexpr += 1; rec = dict(rec); rec["ie"] = nexpr; out.append(json.dumps(rec, separators=(",", ":"))); return nexpr
def const(n, us=()):
    k = (name_of[n], tuple(us))
    if k not in consts: consts[k] = add_expr({"const": {"name": name_of[n], "us": list(us)}})
    return consts[k]
for n in ("Bool", "Bool.true", "Eq", "Eq.refl"): 
    if n not in name_of: sys.exit(f"missing {n} in export")
for d in decls:
    if d not in name_of: sys.exit(f"missing {d} in export")
    bool_ = const("Bool"); tru = const("Bool.true"); dd = const(d)
    eq = const("Eq", [lvl1]); refl = const("Eq.refl", [lvl1])
    ty = add_expr({"app": {"fn": add_expr({"app": {"fn": add_expr({"app": {"fn": eq, "arg": bool_}}), "arg": dd}}), "arg": tru}})
    val = add_expr({"app": {"fn": add_expr({"app": {"fn": refl, "arg": bool_}}), "arg": tru}})
    tn = add_name(d + "_eq_true")
    out.append(json.dumps({"thm": {"name": tn, "levelParams": [], "type": ty, "value": val, "all": [tn]}}, separators=(",", ":")))
    print("added", d + "_eq_true")
open(dst, "w").write("\n".join(out) + "\n")
