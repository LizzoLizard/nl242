# GitHub & Zenodo Release Layout + Publication Checklist

This document specifies the exact clean repository layout to publish on GitHub, archive on **Zenodo** (for a permanent citable DOI), and submit to **arXiv (`math.CO` / `cs.IT`)** and **IACR ePrint**.

---

## Recommended Clean Repository Structure

Create a fresh public GitHub repository (e.g., `balanced-nl242-lean4`) with this clean layout — **do not** dump raw scratch logs, temporary `.tgz` transfer bundles, or `.olean` build artifacts into Git:

```text
balanced-nl242-lean4/
├── README.md                        # Plain-English explainer + quick verification + trust boundary
├── LICENSE                          # MIT or Apache-2.0 for code; CC-BY-4.0 for paper/docs
├── .zenodo.json                     # Auto-populates Zenodo metadata when tagging a GitHub release
├── SHA256SUMS.txt                   # Checksums for all Lean files, certificates, and C++ sources
├── paper/
│   ├── paper.tex                    # Self-contained LaTeX manuscript (compiles on Overleaf/arXiv)
│   └── paper.pdf                    # Compiled PDF (generate via Overleaf or TeX Live)
├── lean/
│   ├── LEAN_PROOF.md                # Full module-by-module Lean 4 technical documentation
│   ├── replay_all.sh                # Sequential low-RAM (~1–1.7 GB) replay of all 68+ modules
│   ├── gen_t94_lean.py              # Reproducible generator for t=94 certificate modules
│   ├── gen_t96_centered.py          # Reproducible generator for t=96 centered modules
│   └── src/                         # All 68+ zero-Mathlib .lean files (no build/*.olean!)
├── colab/
│   ├── verify_nl242_colab.ipynb     # 1-click free Google Colab verification notebook
│   └── nl242_lean_colab.tar.gz      # Standalone 249 KB Lean source bundle
├── certificates/
│   ├── frontier_input.json          # 237 baseline excluded 7D sections
│   ├── remaining_profiles.tsv       # Full frontier table
│   ├── t94_anchor_pair_certs.json   # All t=94 Farkas + 205 anchor-pair certs
│   ├── t96_centered_certs.json      # t=96 (2,47,27) and (1,54,24) centered/residual certs
│   └── ...                          # Final t=96 & t=98 certificates once complete
└── enumerators/
    ├── README.md                    # Exact g++/clang++ build & replay commands + positive controls
    ├── sel_e.cpp                    # 7D rank-6 exception-weight enumerator
    ├── flag_sections.cpp            # 7D flag-section enumerator (with positive control)
    ├── check_centered_profiles.py   # Offline Python/C++ replay for t=96 centered profiles
    └── check_03139.py               # Offline replay for t=96 (0,31,39)
```

---

## Step-by-Step Publishing Workflow

### 1. Finalize Scope Before Minting the DOI
- **If $t = 96$ and $t = 98$ close completely:**
  1. Generate and kernel-verify the final Lean certificate modules (strictly sequentially, 1 `lean` process at a time).
  2. Update the three `% [TODO: ...]` blocks in `paper/paper.tex` (Title, Abstract, Section 6/7) and `README.md` with the final theorem counts and complete `nl_bal(9) = 240` headline theorem.
  3. Rebuild `nl242_lean_colab.tar.gz` and run a fresh end-to-end replay on Google Colab from zero cache to verify 100% clean pass.
- **If publishing the current structural + $t \le 94$ milestone first:**
  1. `paper/paper.tex` and `README.md` are **already scoped honestly** to the exact 68-module verified milestone ($t \le 94$ excluded, $\Delta_F \ge -128$, plus all unconditional structural theorems and `t = 98, r = 6, |Z| = 144`).
  2. Simply compile `paper.tex` to PDF (Overleaf compiles it with zero extra packages) and replace `[GITHUB_URL]` / `[ZENODO_DOI]`.

### 2. Mint a Permanent Zenodo DOI via GitHub
1. Push the clean repository to GitHub (`main` branch).
2. Log in to [zenodo.org](https://zenodo.org/) using your GitHub account.
3. Go to **GitHub settings** inside Zenodo and toggle **ON** your repository (`balanced-nl242-lean4`).
4. On GitHub, create a Release (e.g., tag `v1.0.0`, title `"Balanced 9-Variable NL242 — Lean 4 Formalization and Proofs"`).
5. Zenodo automatically archives the snapshot and mints a permanent DOI (e.g., `10.5281/zenodo.XXXXXXX`).
6. Copy that DOI into `paper/paper.tex` and `README.md` (use the Zenodo **concept DOI** so citations always resolve to the latest version!).

### 3. Preprint & Community Distribution
- **IACR Cryptology ePrint Archive** (`eprint.iacr.org`): fast turnaround, no endorser required, heavily read by Boolean-function / symmetric-crypto researchers (Kavut, Maitra, Carlet, Mesnager, Stanica, etc.).
- **arXiv** (`math.CO` primary, `cs.IT` / `cs.LO` cross-list): requires an endorser on first submission in `math.CO` (if needed, a Lean/formal-math researcher or IACR contact can endorse once they see the clean LaTeX + Colab replay).
- **Lean Zulip (`#announce` / `#mathematics`)**: share the zero-Mathlib 1-click Colab notebook + theorem list once the final version is tagged — the Lean community loves zero-dependency self-contained formalizations with clear trust boundaries!
