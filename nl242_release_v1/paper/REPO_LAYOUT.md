# GitHub & Zenodo Release Layout

This document specifies the published repository layout for `https://github.com/LizzoLizard/nl242` and the Zenodo archive (`https://doi.org/10.5281/zenodo.24447815`).

---

## Published Release Structure (`nl242_release_v1/`)

```text
nl242_release_v1/
├── README.md                            # Plain-English explainer, 1-click Colab verification, trust boundary & citation
├── .zenodo.json                         # Zenodo release metadata (79 Lean modules + 7 replay packets)
├── SHA256SUMS                           # Top-level SHA-256 manifest of all release files
├── paper/
│   ├── paper.tex / paper.pdf            # Main LaTeX manuscript (nl_bal(9) = 240)
│   ├── companion.tex / companion.pdf    # Guided walkthrough of the proof
│   ├── t100.tex / t100.pdf              # Full t = 100 proof (ranks <=4, 6, 8 + Lemma 5.2 wt16 proof)
│   └── REPO_LAYOUT.md                   # This file
├── lean/
│   ├── LEAN_PROOF.md                    # Module-by-module Lean 4 documentation + resolved 2026-11-22 replay audit
│   ├── verify_nl242_colab.ipynb         # 1-click free Google Colab verification notebook
│   └── nl242_lean_colab.tar.gz          # Standalone 389 KB zero-Mathlib Lean 4.15.0 archive (79 modules)
├── release_packets/
│   ├── SHA256SUMS                       # SHA-256 manifest of all 7 replay packets
│   ├── nl242_t96_closure.zip            # t = 96 quartic four-cell closure
│   ├── nl242_t98_closure.zip            # t = 98 quartic + dual + orbit-mass closure
│   ├── nl242_middle_closure.zip         # t = 104–108 middle-window closure
│   ├── nl242_top_closure.zip            # t >= 100 & t = 84 closure (104 files, incl. t = 100 rank-6 audit verifiers)
│   ├── nl242_endpoint_closure.zip       # Direct t = 114, 116 endpoint closure
│   ├── nl242_endpoint_crosscheck.zip    # Independent RM(3,5) code-lift cross-check for t = 116, k = 16
│   └── nl244_verify.zip                 # Independent re-verification of rho(1, 9) < 244
└── t100_r6_audit/
    ├── verify_z128_reductions.cpp       # Mirror of t100/z128/verify_z128_reductions.cpp (Passes 1–5)
    └── verify_z112_all45_exact.cpp      # Mirror of t100/z112/verify_z112_all45_exact.cpp (45 pairs, 7 positive controls)
```

---

## Verification Quickstart

- **Lean 4 (79 zero-Mathlib modules):** Open `lean/verify_nl242_colab.ipynb` in Google Colab (https://colab.research.google.com/github/LizzoLizard/nl242/blob/main/nl242_release_v1/lean/verify_nl242_colab.ipynb) or unpack `lean/nl242_lean_colab.tar.gz` locally and run `./replay_all.sh`.
- **Release checksums:** From `nl242_release_v1/`, run `shasum -a 256 -c SHA256SUMS` and `(cd release_packets && shasum -a 256 -c SHA256SUMS)`.
- **Top-window + `t = 100` rank-6 quick replay:** Unpack `release_packets/nl242_top_closure.zip` and run `shasum -a 256 -c SHA256SUMS && bash verify_quick.sh` (`10/10` steps).
