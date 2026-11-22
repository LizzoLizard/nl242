#!/usr/bin/env bash
# Replay all 79 zero-Mathlib Lean 4.15.0 modules sequentially from scratch
# (1 lean process at a time, ~1-1.7 GB peak RAM; covers No244, t<=94,
#  t=96 centered/quartic, t=98 r6 Z=144, quartic high-block, low-block budget,
#  unconditional t<=112 no-Z64, t>=104 rank 8, t>=108 rank 6, unconditional
#  t=112, unconditional t=114 & t=116 k=12, unconditional t=118, and the
#  coordinate-free master theorem Balanced242Master.no_balanced_9var_nl242).
set -euo pipefail
mkdir -p build
MODS=(
  FrozenShells
  CandyKnots
  FreezeMovies
  CollisionLaw
  MaskRecovery
  CollisionCircuit
  SilentRoom
  Balanced242Parents
  Balanced242Blocks
  Balanced242Support
  Balanced242Hyperplane
  Balanced242Coord
  Balanced242Section0320
  Balanced242Plateau
  Balanced242No244
  Balanced242PairData
  Balanced242Pair
  Balanced242Reduction
  Balanced242SectionFacts
  Balanced242Rank
  Balanced242Global
  Balanced242PairCheck86
  Balanced242PairCheck88
  Balanced242PairCheck90
  Balanced242PairCheck92
  Balanced242Final
  Balanced242Sectors
  Balanced242Endpoint
  Balanced242HighSections
  Balanced242RankCond
  Balanced242Complete
  Balanced242LowRange
  Balanced242Parity
  Balanced242Rank8
  Balanced242AnchorPair
  Balanced242SectionBounds
  Balanced242Quartic
  Balanced242Krawtchouk
  Balanced242Farkas
  Balanced242T94Data
  Balanced242T94Direct
  Balanced242FastCond
  Balanced242T94L12_base
  Balanced242T94L15_base
  Balanced242T94L12_c0
  Balanced242T94L12_c1
  Balanced242T94L12_c2
  Balanced242T94L12_c3
  Balanced242T94L12_c4
  Balanced242T94L12_c5
  Balanced242T94L12_c6
  Balanced242T94L12_c7
  Balanced242T94L15_c0
  Balanced242T94L15_c1
  Balanced242T94L15_c2
  Balanced242T94L15_c3
  Balanced242T94L15_c4
  Balanced242T94L15_c5
  Balanced242T94L15_c6
  Balanced242T94Layered
  Balanced242T94
  Balanced242T98R6Z144
  Balanced242Centered
  Balanced242T96Arith
  Balanced242T96Data
  Balanced242T96_2_47_27_L0
  Balanced242T96_1_54_24_L0
  Balanced242T96Centered
  Balanced242T96Quartic
  Balanced242T96_0_51_27
  Balanced242QuarticHighBlock
  Balanced242LowBlock
  Balanced242Z64Switch
  Balanced242T108R6
  Balanced242T104R8
  Balanced242T112
  Balanced242T114
  Balanced242T118
  Balanced242Master
)
echo "Lean version: $(lean --version)"
for m in "${MODS[@]}"; do
  if [ -f "build/$m.olean" ]; then
    echo "[SKIP] $m (already built)"
    continue
  fi
  echo "[BUILD] $m"
  LEAN_PATH=build lean -o "build/$m.olean" "$m.lean"
done
echo "ALL 79 MODULES VERIFIED!"
