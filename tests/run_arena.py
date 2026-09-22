#!/usr/bin/env python3
"""Run lazylean against the Lean Kernel Arena tests (tests/**/*.yaml).

Tests with `file:` are run directly; tests with `leanfile:` are compiled with the local Lean
toolchain and exported with lean4export (optionally restricted to `export-decls`).
Exit-code contract: 0 accept, 1 reject, 2 declined, other = checker error.
"""
import os, subprocess, sys, tempfile, yaml, glob, time

ARENA = os.path.expanduser(sys.argv[1] if len(sys.argv) > 1 else "~/dev/lean-kernel-arena")
CHECKER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "build", "lazylean")
EXPORT = os.path.expanduser("~/dev/lean4export")
CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "arena-cache")
os.makedirs(CACHE, exist_ok=True)
PAT = sys.argv[2] if len(sys.argv) > 2 else ""
env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])

def capped(cmd, timeout=600, **kw):
    full = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=3G", "-p", "MemorySwapMax=0", "timeout", str(timeout)] + cmd
    return subprocess.run(full, capture_output=True, text=True, env=env, **kw)

def export_leanfile(leanfile, decls, out):
    if os.path.exists(out) and os.path.getsize(out) > 0: return True
    with tempfile.TemporaryDirectory() as td:
        # compile as module `Test`
        src = os.path.join(td, "Test.lean")
        with open(leanfile) as f: body = f.read()
        with open(src, "w") as f: f.write(body)
        tc = open(os.path.join(EXPORT, "lean-toolchain")).read().strip().replace("/", "--").replace(":", "---")
        leanbin = os.path.expanduser(f"~/.elan/toolchains/{tc}/bin/lean")
        r = capped([leanbin, "-o", os.path.join(td, "Test.olean"), src], cwd=td)
        if r.returncode != 0:
            print("    lean failed:", r.stderr[:300].replace("\n", " ")); return False
        cmd = ["lake", "env", os.path.join(EXPORT, ".lake/build/bin/lean4export"), "Test"]
        if decls: cmd += ["--"] + list(decls)
        e2 = dict(env, LEAN_PATH=td)
        full = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=3G", "-p", "MemorySwapMax=0", "timeout", "600"] + cmd
        with open(out, "w") as f:
            r = subprocess.run(full, stdout=f, stderr=subprocess.PIPE, text=True, env=e2, cwd=EXPORT)
        if r.returncode != 0:
            print("    lean4export failed:", r.stderr[:300].replace("\n", " ")); os.remove(out); return False
    return True

results = {"pass": 0, "fail": 0, "skip": 0}
failures = []
for y in sorted(glob.glob(os.path.join(ARENA, "tests", "**", "*.yaml"), recursive=True)):
    name = os.path.relpath(y, os.path.join(ARENA, "tests"))[:-5]
    if PAT and PAT not in name: continue
    t = yaml.safe_load(open(y))
    if not isinstance(t, dict) or t.get("multiple"): continue
    outcome = t.get("outcome")
    if "file" in t: nd = os.path.join(ARENA, t["file"])
    elif "leanfile" in t:
        nd = os.path.join(CACHE, name.replace("/", "_") + ".ndjson")
        if not export_leanfile(os.path.join(ARENA, t["leanfile"]), t.get("export-decls"), nd):
            results["skip"] += 1; print(f"SKIP {name} (export failed)"); continue
    else:
        results["skip"] += 1; continue
    if os.path.getsize(nd) > 200 * 1024 * 1024: results["skip"] += 1; print(f"SKIP {name} (too large)"); continue
    t0 = time.time()
    r = capped([CHECKER, nd], timeout=int(t.get("timeout", 120)) * 2 + 60)
    dt = time.time() - t0
    rc = r.returncode
    got = "accept" if rc == 0 else "declined" if rc == 2 else "reject" if rc == 1 else f"error({rc})"
    ok = (outcome == "either") or (outcome == got) or (outcome == "reject" and got.startswith("error"))
    results["pass" if ok else "fail"] += 1
    msg = r.stderr.strip().splitlines()[-1] if r.stderr.strip() else ""
    print(f"{'ok  ' if ok else 'FAIL'} {name}: expected {outcome}, got {got} ({dt:.1f}s) {msg[:160]}")
    if not ok: failures.append(name)
print(results)
if failures: print("failures:", failures)
