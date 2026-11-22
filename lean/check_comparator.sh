#!/usr/bin/env bash
# check_comparator.sh — Trusted-base audit + Comparator check for NL242Challenge.
#
# Usage:
#   ./check_comparator.sh                # uses `comparator` if installed, else runs the
#                                        # built-in Lean 4 kernel AST & axiom checker
#   LEAN_PATH=... ./check_comparator.sh  # reuse existing compiled .olean directories
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "=== [1/3] Auditing trusted base (ChallengeDefs.lean & Challenge.lean) ==="
python3 - <<'PY'
import pathlib, re

def strip_comments(s: str) -> str:
    return re.sub(r'--.*', '', re.sub(r'/-.*?-/', '', s, flags=re.S))

defs_txt = strip_comments(pathlib.Path("ChallengeDefs.lean").read_text())
defs_imps = re.findall(r'^\s*import\s+(\S+)', defs_txt, re.M)
assert defs_imps == [], f"ChallengeDefs.lean must have zero imports, got {defs_imps}"

chal_txt = strip_comments(pathlib.Path("Challenge.lean").read_text())
chal_imps = re.findall(r'^\s*import\s+(\S+)', chal_txt, re.M)
assert chal_imps == ["ChallengeDefs"], f"Challenge.lean must import only ChallengeDefs, got {chal_imps}"

sol_txt = strip_comments(pathlib.Path("Solution.lean").read_text())
bad_sol = re.findall(r'\b(sorry|native_decide|axiom|admit)\b', sol_txt)
assert not bad_sol, f"Disallowed tokens in Solution.lean: {bad_sol}"

src_files = sorted(pathlib.Path("src").glob("*.lean"))
assert len(src_files) == 79, f"Expected 79 modules in src/, got {len(src_files)}"
for p in src_files:
    bad = re.findall(r'\b(sorry|native_decide|axiom|admit)\b', strip_comments(p.read_text()))
    assert not bad, f"Disallowed tokens in {p}: {bad}"

print("PASS: ChallengeDefs.lean has 0 imports; Challenge.lean imports only ChallengeDefs;")
print("      Solution.lean + all 79 src/*.lean files have 0 sorry, 0 native_decide, 0 custom axiom.")
PY

if [ -n "${COMPARATOR_BIN:-}" ] || command -v comparator >/dev/null 2>&1; then
  CMP="${COMPARATOR_BIN:-comparator}"
  echo "=== [2/3] Running official leanprover/comparator ($CMP) ==="
  lake env "$CMP" config.json
  echo "=== [3/3] Official Comparator verification PASSED! ==="
  exit 0
fi

echo "=== [2/3] Checking compiled .olean artifacts ==="
if [ -z "${LEAN_PATH:-}" ]; then
  if [ -f ".lake/build/lib/Challenge.olean" ] && [ -f ".lake/build/lib/Solution.olean" ]; then
    export LEAN_PATH="$SCRIPT_DIR/.lake/build/lib"
  elif [ -f "src/build/Balanced242Master.olean" ]; then
    mkdir -p src/build
    LEAN_PATH="$SCRIPT_DIR/src/build" lean -o "$SCRIPT_DIR/src/build/ChallengeDefs.olean" ChallengeDefs.lean
    LEAN_PATH="$SCRIPT_DIR/src/build" lean -o "$SCRIPT_DIR/src/build/Challenge.olean" Challenge.lean
    LEAN_PATH="$SCRIPT_DIR/src/build" lean -o "$SCRIPT_DIR/src/build/Solution.olean" Solution.lean
    export LEAN_PATH="$SCRIPT_DIR/src/build"
  else
    echo "No prebuilt .olean directory found; running 'lake build Challenge Solution'..."
    lake build Challenge Solution
    export LEAN_PATH="$SCRIPT_DIR/.lake/build/lib"
  fi
fi

echo "=== [3/3] Running Lean 4 kernel AST + transitive-definition + axiom check ==="
TMP_CHECK="$(mktemp "${TMPDIR:-/tmp}/nl242_cmp_XXXXXX.lean")"
trap 'rm -f "$TMP_CHECK"' EXIT
cat > "$TMP_CHECK" <<'LEAN'
import Lean

open Lean

def collectTypeConsts (env : Environment) (roots : List Name) : NameSet :=
  Id.run do
    let mut visited : NameSet := {}
    let mut work : List Name := roots
    while !work.isEmpty do
      let n :: rest := work | break
      work := rest
      if visited.contains n then continue
      visited := visited.insert n
      if let some ci := env.find? n then
        for c in ci.type.getUsedConstants do
          if !visited.contains c then work := c :: work
        if let some v := ci.value? then
          match ci with
          | .thmInfo _ => pure ()
          | _ =>
            for c in v.getUsedConstants do
              if !visited.contains c then work := c :: work
    return visited

def quotKindEq : QuotKind → QuotKind → Bool
  | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
  | _, _ => false

def constDeclEq (a b : ConstantInfo) : Bool :=
  match a, b with
  | .defnInfo x, .defnInfo y =>
      x.levelParams == y.levelParams && x.type == y.type && x.value == y.value
  | .axiomInfo x, .axiomInfo y =>
      x.levelParams == y.levelParams && x.type == y.type
  | .inductInfo x, .inductInfo y =>
      x.levelParams == y.levelParams && x.type == y.type &&
      x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.ctors == y.ctors
  | .ctorInfo x, .ctorInfo y =>
      x.levelParams == y.levelParams && x.type == y.type &&
      x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams && x.numFields == y.numFields
  | .recInfo x, .recInfo y =>
      x.levelParams == y.levelParams && x.type == y.type &&
      x.numParams == y.numParams && x.numIndices == y.numIndices && x.numMotives == y.numMotives
  | .quotInfo x, .quotInfo y =>
      x.levelParams == y.levelParams && x.type == y.type && quotKindEq x.kind y.kind
  | .opaqueInfo x, .opaqueInfo y =>
      x.levelParams == y.levelParams && x.type == y.type && x.value == y.value
  | .thmInfo x, .thmInfo y =>
      x.levelParams == y.levelParams && x.type == y.type
  | _, _ => false

structure Cfg where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  permitted_axioms : Array String
  deriving FromJson

def main (args : List String) : IO Unit := do
  let cfgPath := args[0]?.getD "config.json"
  let txt ← IO.FS.readFile cfgPath
  let cfg : Cfg ← IO.ofExcept <| (Json.parse txt >>= fromJson?)
  initSearchPath (← findSysroot)
  let envC ← importModules #[{ module := cfg.challenge_module.toName }] {} (trustLevel := 0)
  let envS ← importModules #[{ module := cfg.solution_module.toName }] {} (trustLevel := 0)
  let allowed : NameSet := cfg.permitted_axioms.foldl (fun s a => s.insert a.toName) {}
  let mut rootTypes : List Name := []
  for thmStr in cfg.theorem_names do
    let nm := thmStr.toName
    let some (.thmInfo ciC) := envC.find? nm
      | throw <| IO.userError s!"Missing theorem in {cfg.challenge_module}: {nm}"
    let some (.thmInfo ciS) := envS.find? nm
      | throw <| IO.userError s!"Missing theorem in {cfg.solution_module}: {nm}"
    if ciC.levelParams != ciS.levelParams || ciC.type != ciS.type then
      throw <| IO.userError s!"Statement MISMATCH for {nm}"
    for c in ciC.type.getUsedConstants do
      rootTypes := c :: rootTypes
    let (_, st) := (CollectAxioms.collect nm).run envS {}
    for ax in st.axioms do
      if !allowed.contains ax then
        throw <| IO.userError s!"Disallowed axiom {ax} in {nm}"
    IO.println s!"[PASS] {nm}  axioms={st.axioms.toList}"
  let depConsts := collectTypeConsts envC rootTypes
  let mut checked := 0
  for c in depConsts do
    let some a := envC.find? c
      | throw <| IO.userError s!"Missing dep {c} in Challenge"
    let some b := envS.find? c
      | throw <| IO.userError s!"Missing dep {c} in Solution"
    if !constDeclEq a b then
      throw <| IO.userError s!"Definition MISMATCH on transitive dependency {c}"
    checked := checked + 1
  IO.println s!"ALL {cfg.theorem_names.size} THEOREMS MATCH SYNTACTICALLY ({checked} transitive type definitions identical, axioms within whitelist)!"
LEAN

lean --run "$TMP_CHECK" config.json
