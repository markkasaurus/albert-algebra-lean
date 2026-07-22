#!/usr/bin/env bash

set -euo pipefail

repo_root="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
challenge="$repo_root/Challenge.lean"

if [[ -e "$challenge" ]]; then
  echo "Challenge.lean already exists; refusing to overwrite it." >&2
  exit 1
fi

trap 'rm -f "$challenge"' EXIT

cat > "$challenge" <<'EOF'
import AlbertAlgebraStatement

namespace Albert.Verification

universe u

theorem jordan_identity : Statement.jordanIdentity := by
  sorry

theorem glennie_violation : Statement.glennieViolation := by
  sorry

theorem non_speciality : Statement.nonSpeciality.{u} := by
  sorry

end Albert.Verification
EOF

cd "$repo_root"
lake env comparator Verification/comparator.json
