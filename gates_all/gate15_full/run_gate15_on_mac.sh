#!/bin/bash
# Gate 15: Lean-check all 1,348,864 one-bit lots of Segment 33. Read-only outside this folder.
set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
pwd
shasum -a 256 -c SHA256SUMS.txt | grep -v ': OK$'; echo "HASH_CHECK_DONE"
nice -n 19 lake build Gate15.All > gate15_build.log 2>&1
echo "BUILD_EXIT=$?"
tail -2 gate15_build.log
printf 'import Gate15.All\nopen Gate15\n#print axioms half_child_descends\n#print axioms allOneBit_sound\n#print axioms lots0000_drop\n#print axioms lots1348_drop\n#print axioms control_open_sibling\n' > Gate15Axioms.lean
lake env lean Gate15Axioms.lean
echo "AXIOM_EXIT=$?"
echo "CHUNKS_BUILT=$(ls .lake/build/lib/lean/Gate15/Lots/ 2>/dev/null | grep -c '\.olean$') (expected 1349)"
grep -h "_count : " Gate15/Lots/*.lean | awk '{s+=$6} END {print "LOTS_IN_CHUNKS=" s " (expected 1348864)"}'
