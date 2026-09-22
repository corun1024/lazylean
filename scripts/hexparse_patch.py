# Teach lean4export's Export/Parse.lean to read natVal literals written as 0x-prefixed hex
# (divide-and-conquer, so million-bit literals parse in near-linear time).
import sys
p = sys.argv[1]; s = open(p).read()
if 'hexToNat?' in s: print("already patched"); sys.exit(0)
helpers = '''private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Value of the hex digits `a[lo:hi]`. -/
private partial def hexToNatAux (a : Array Char) (lo hi : Nat) : Option Nat :=
  let n := hi - lo
  if n == 0 then none
  else if n ≤ 16 then
    (List.range n).foldl (fun acc i => acc.bind fun v => (hexDigit? a[lo + i]!).map fun d => v * 16 + d) (some 0)
  else
    let k := n / 2
    match hexToNatAux a lo (lo + k), hexToNatAux a (lo + k) hi with
    | some hi', some lo' => some ((hi' <<< (4 * (n - k))) + lo')
    | _, _ => none

/-- `0x…` hex literal to `Nat`. -/
private def hexToNat? (s : String) : Option Nat :=
  let a := s.toList.toArray
  if a.size > 2 && a[0]! == '0' && a[1]! == 'x' then hexToNatAux a 2 a.size else none

def parseExprNatLit (json : Json) : M Expr := do
  let .str natValStr := json | fail s!"Expr.lit natVal invalid"
  let some natVal := (if natValStr.startsWith "0x" then hexToNat? natValStr else String.toNat? natValStr)
    | fail s!"Expr.lit natVal invalid"
'''
old = '''def parseExprNatLit (json : Json) : M Expr := do
  let .str natValStr := json | fail s!"Expr.lit natVal invalid"
  let some natVal := String.toNat? natValStr | fail s!"Expr.lit natVal invalid"
'''
assert s.count(old) == 1, "pattern not found"
open(p, 'w').write(s.replace(old, helpers)); print("patched", p)
