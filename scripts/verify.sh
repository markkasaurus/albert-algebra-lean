#!/usr/bin/env bash

set -euo pipefail

repo_root="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

cd "$repo_root"

build_log="$tmpdir/build.log"
axioms_log="$tmpdir/axioms.log"
normalized_axioms_log="$tmpdir/normalized-axioms.log"
expected_axioms_log="$tmpdir/expected-axioms.log"
statement_imports_log="$tmpdir/statement-imports.log"
expected_statement_imports_log="$tmpdir/expected-statement-imports.log"

if ! grep -q '"name": "albertAlgebra"' lake-manifest.json; then
  echo "The lockfile package name does not match the standalone package." >&2
  exit 1
fi

echo "[1/8] Building the repository"
lake build 2>&1 | tee "$build_log"
if grep -nE "warning:|error:" "$build_log" >/dev/null; then
  echo "Build output contains warnings or errors." >&2
  grep -nE "warning:|error:" "$build_log" >&2
  exit 1
fi

echo
echo "[2/8] Checking Lean source style"
lake exe lint-style \
  AlbertAlgebra \
  AlbertAlgebra.Basic \
  AlbertAlgebra.CoordinateProduct \
  AlbertAlgebra.Coordinates \
  AlbertAlgebra.GlennieIdentity \
  AlbertAlgebra.GlenniePolynomial \
  AlbertAlgebra.GlennieWitness \
  AlbertAlgebra.JordanIdentity \
  AlbertAlgebra.NonSpecial \
  AlbertAlgebra.Octonion \
  AlbertAlgebra.OctonionIdentities \
  AlbertAlgebraStatement \
  AlbertAlgebraVerification \
  Verification.Axioms

echo
echo "[3/8] Checking axiom dependencies"
lake env lean Verification/Axioms.lean 2>&1 | tee "$axioms_log"
if grep -n "sorryAx" "$axioms_log" >/dev/null; then
  echo "Unexpected sorryAx dependency found." >&2
  exit 1
fi
awk '
  /depends on axioms:/ {
    record = $0
    while (record !~ /]$/ && getline > 0) record = record " " $0
    gsub(/[[:space:]]+/, " ", record)
    print record
  }
' "$axioms_log" > "$normalized_axioms_log"
cat > "$expected_axioms_log" <<'EOF'
'Octonion.finrank_eq_eight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Albert.Coordinates.finrank_eq_twenty_seven' depends on axioms: [propext, Classical.choice, Quot.sound]
'Albert.jordan_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Glennie.glennie_identity_in_associative_symmetrization' depends on axioms: [propext, Classical.choice, Quot.sound]
'Albert.GlennieWitness.violates_glennie_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Albert.no_faithful_special_embedding' depends on axioms: [propext, Classical.choice, Quot.sound]
'Albert.Verification.jordan_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Albert.Verification.glennie_violation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Albert.Verification.non_speciality' depends on axioms: [propext, Classical.choice, Quot.sound]
EOF
if ! diff -u "$expected_axioms_log" "$normalized_axioms_log"; then
  echo "Unexpected axiom dependency found." >&2
  exit 1
fi

echo
echo "[4/8] Scanning for placeholders"
placeholder_pattern='(^|[^[:alnum:]_])(sorry|admit|sorryAx)([^[:alnum:]_]|$)'
if grep -RInE "$placeholder_pattern" --include="*.lean" \
    --exclude-dir=".lake" --exclude-dir=".git" . >/dev/null; then
  echo "Unexpected placeholder token found." >&2
  grep -RInE "$placeholder_pattern" --include="*.lean" \
    --exclude-dir=".lake" --exclude-dir=".git" . >&2
  exit 1
fi

echo
echo "[5/8] Scanning for declaration escape hatches"
escape_pattern='^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable)[[:space:]]+)*(axiom|postulate|unsafe|opaque|partial|extern)[[:space:]]|implemented_by'
if grep -RInE "$escape_pattern" --include="*.lean" \
    --exclude-dir=".lake" --exclude-dir=".git" . >/dev/null; then
  echo "Unexpected declaration form found." >&2
  grep -RInE "$escape_pattern" --include="*.lean" \
    --exclude-dir=".lake" --exclude-dir=".git" . >&2
  exit 1
fi

echo
echo "[6/8] Scanning for development artifacts"
if find . -path './.lake' -prune -o -path './.git' -prune -o -print |
    grep -Ei '(^|/)(_scratch|scratch|backup|archive|tmp|output)([._/-]|$)' >/dev/null; then
  echo "Provisional path found." >&2
  exit 1
fi

echo
echo "[7/8] Checking import boundaries"
if grep -RHE '^import ' --include="*.lean" \
    --exclude-dir=".lake" --exclude-dir=".git" . |
    grep -vE ':import (Lake$|Mathlib([.]|$)|AlbertAlgebra([.]|Statement$|Verification$|$))' >/dev/null; then
  echo "A Lean source imports a module outside Lake, Mathlib, or AlbertAlgebra." >&2
  grep -RHE '^import ' --include="*.lean" \
    --exclude-dir=".lake" --exclude-dir=".git" . |
    grep -vE ':import (Lake$|Mathlib([.]|$)|AlbertAlgebra([.]|Statement$|Verification$|$))' >&2
  exit 1
fi

echo
echo "[8/8] Checking the public statement boundary"
grep -E '^import ' AlbertAlgebraStatement.lean > "$statement_imports_log"
cat > "$expected_statement_imports_log" <<'EOF'
import AlbertAlgebra.Basic
import AlbertAlgebra.GlenniePolynomial
import Mathlib.Algebra.Jordan.Basic
import Mathlib.Algebra.Symmetrized
EOF
if ! diff -u "$expected_statement_imports_log" "$statement_imports_log"; then
  echo "The public statement imports proof implementation." >&2
  exit 1
fi

echo
echo "Verification completed successfully."
