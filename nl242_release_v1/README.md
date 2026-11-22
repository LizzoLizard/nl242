# No Balanced 9-Variable Boolean Function Has Nonlinearity 242 — Lean 4 Formalization & Proofs

[![Lean 4.15.0](https://img.shields.io/badge/Lean-4.15.0-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-Zero%20Dependencies-brightgreen.svg)](#verification)
[![Lean](https://img.shields.io/badge/Lean%20formalization-in%20development-informational.svg)](#trust-boundary)
[![Axioms](https://img.shields.io/badge/sorry%20%7C%20native__decide-0%20%7C%200-success.svg)](#trust-boundary)

<!-- [TODO: Insert Zenodo DOI badge after first GitHub release] -->

**The maximum nonlinearity of a balanced nine-variable Boolean function is exactly 240.** Thus $n = 9$ is the smallest odd dimension in which requiring balance strictly lowers the maximum nonlinearity below the covering radius ($240 < 242 \le \rho(1,9)$, whereas balanced functions attain $\rho(1,n) = 0, 2, 12, 56$ for $n = 1, 3, 5, 7$). The **zero-Mathlib Lean 4** master theorem (`79` compiled modules, zero `sorry`) formally reduces the coordinate-free theorem to explicit finite computational hypotheses, each discharged by written reductions (including `paper/t100.tex` for $t = 100$, rank $6$) and SHA-256-manifested replay packets — with the final $t = 114, 116$ endpoint verified by **three independent proofs** (`nl242_endpoint_closure.zip`, `nl242_endpoint_crosscheck.zip`, and `nl244_verify.zip`).

The repository contains the following materials.
- the mathematical manuscript (`paper/paper.tex`), and a companion guide (`paper/companion.tex`) that walks through the proof in smaller steps;
- a **zero-Mathlib Lean 4.15.0** formalization with **79 compiled modules** in the replay archive, zero `sorry`, zero `native_decide`, and zero custom axioms (culminating in the coordinate-free master theorems `Balanced242Master.no_balanced_9var_nl242_direct` and `Balanced242Master.no_balanced_9var_nl242`);
- SHA-256-manifested replay packets for the finite enumerations: `nl242_t96_closure.zip`, `nl242_t98_closure.zip`, `nl242_middle_closure.zip`, `nl242_top_closure.zip`, `nl242_endpoint_closure.zip`, `nl242_endpoint_crosscheck.zip` and `nl244_verify.zip`.

## Computer-assisted proof

This is a computer-assisted proof. Its correctness includes the correctness of our code. That is normal for results like this, so we publish all of the code:
- every enumerator and verifier ships as source in the replay packets, with expected outputs and positive controls;
- the heaviest steps were replayed independently from those packets.

The Lean formalization covers the structural theorems (Layers A and B below). It does **not** cover the large finite enumerations (Layer C).

The direct endpoint packet excludes agreement counts 114 and 116. Lean checks the plane switch to complementary eight-variable tables. The finite enumeration checks all 8,192 high sign cosets and excludes the low complements of the five surviving signings. The proof, source and replay commands are in `nl242_endpoint_closure.zip`. `nl242_endpoint_crosscheck.zip` repeats the 116 calculation with separate code. It rebuilds all 70 admissible high blocks without merging equivalent ones and scores every quadratic Q by direct Walsh transforms. It finds the same counts: maxima 2272 and 2304, and 81,920 equality cases, all with peak 28. The earlier unrestricted route credits Wang, Lou and Wang (arXiv:2610.17871) and rechecks their argument and the Brier–Langevin classification in `nl244_verify.zip`. The complete rank-6 reductions and audited closures at $t = 100$ (including the Branch I weight-16 normalization and 22-bit subcube syndrome proof, hand closures of Branches II-B2/II-B3 and $(h,p)=(0,0)$, and the full 45-pair $|Z|=112$ scan killing all 111/111 live cases with 7/7 positive controls) are documented in `paper/t100.tex` and packaged directly inside `nl242_top_closure.zip` (`104` SHA-256-verified files: `t100/z128/verify_z128_reductions.cpp`, `t100/z112/check_small_masks.cpp`, and `t100/z112/verify_z112_all45_exact.cpp`, mirrored in `t100_r6_audit/`).

---

## Plain-English Explainer (For Non-Specialists)

### What is the problem?
Imagine a **9-dimensional grid with $2^9 = 512$ corners** (every 9-bit string from `000000000` to `111111111`). You want to color every corner either **black** (`0`) or **white** (`1`) under two competing rules:

1. **Balance:** Exactly **256 black** and **256 white** corners (no bias toward either color).
2. **Maximum "unpredictability" (nonlinearity 242):** Now imagine all **1,024 possible straight "stripe patterns"** across the 9D grid (every linear/affine Boolean function and its inverse). Your coloring must disagree with **every single stripe pattern** on at least **242 of the 512 corners** — equivalently, no straight stripe pattern can correlate with your coloring by more than **28** out of 512.

Why is this hard and famous?
- In cryptography (S-boxes and stream ciphers), high nonlinearity measures resistance against linear attacks, and balance prevents statistical bias.
- Standard constructions easily reach **240** (balanced).
- In **2006–2007**, Kavut, Maitra, and Yücel stunned the field by finding **unbalanced** 9-variable colorings that reach **242**.
- For nearly **20 years**, nobody has been able to build a **balanced** coloring at 242 — nor prove that one is impossible.
- Brute force is hopeless: there are $\binom{512}{256} \approx 4.7 \times 10^{152}$ balanced colorings (far more than atoms in the observable universe).

### How does our proof attack an impossible-to-search space?
Instead of testing individual colorings, we prove **global structural laws about their "shadows"** (slices):

1. **Slice the 9D cube in half** into two 8D cubes ($f$ and $g$, 256 corners each), and measure how many corners agree between the two halves (the parameter $t$).
2. **Hidden geometry in the spectrum:** When you take the Fourier/Walsh spectrum of the disagreement between $f$ and $g$, the *signs* of the spectrum cannot be arbitrary — they must form a rigid **quadratic surface** (`RM(2, 8)`). That single rigidity law triggers a chain reaction:
   - **Rank-8 Parity Law:** The full-rank geometry occurs *if and only if* a specific count of exceptional frequencies is odd.
   - **63/64 Coupled Slicing Law:** Slice the 8D cube by any hyperplane into two 7D halves, then slice again along all 127 directions — **exactly 63** produce rank-4 shadows on *both* halves simultaneously, and **exactly 64** produce rank-6 shadows on *both* halves.
   - **Barycenter & Coding Collisions:** Centering on an odd-sized class's $\mathbb{F}_2$-barycenter turns a second class into a linear parity marker, feeding exact integer linear programming (Farkas) contradictions and classical coding-theory barriers (Griesmer & sphere-packing bounds, e.g., proving no `[24, 8, ≥10]₂` binary linear code can exist).
3. **Checked by machine, in two ways:**
   - **Lean 4 (in development).** The structural theorems are checked by the Lean 4.15.0 kernel, with no external math library (zero Mathlib) and no shortcuts (`sorry` / `native_decide`). The archive replays on a free Google Colab CPU runtime in under 1.7 GB RAM.
   - **Exhaustive computation.** The finite case checks are done by published C++/Python verifiers, which anyone can rerun.

---

## Quick Verification (1-Click Colab or Local)

### Option A: One-Click Google Colab (Free CPU Runtime, ~1–1.7 GB RAM)
1. Open `colab/verify_nl242_colab.ipynb` in Google Colab.
2. Upload `colab/nl242_lean_colab.tar.gz` (389 KB) when prompted.
3. Click **Run All**. It installs Lean 4.15.0 via `elan`, audits zero `sorry`/`native_decide`/`axiom`, and compiles all **79 modules** in the archive sequentially from scratch.

### Option B: Local Replay (macOS / Linux)
Requires only `lean` v4.15.0 (no Mathlib, no Lake cache needed):
```bash
tar -xzf colab/nl242_lean_colab.tar.gz
cd nl242_lean
./replay_all.sh
```

To audit that zero `sorry`, zero `native_decide`, and zero custom `axiom` declarations appear anywhere in the 79 modules:
```bash
python3 -c "
import pathlib, re
for p in sorted(pathlib.Path('nl242_lean').glob('*.lean')):
    s = re.sub(r'--.*', '', re.sub(r'/-.*?-/', '', p.read_text(), flags=re.S))
    bad = re.findall(r'\b(sorry|native_decide|axiom|admit)\b', s)
    assert not bad, (p, bad)
print('ALL 79 MODULES CLEAN: 0 sorry, 0 native_decide, 0 custom axiom')
"
```

---

## Trust Boundary

We explicitly separate the verification into three transparent layers (see Section 7 of `paper/paper.tex`):

| Layer | Trusted Base | What It Proves |
|---|---|---|
| **Layer A** | **Lean 4.15.0 kernel only** (standard axioms `[propext, (Classical.choice,) Quot.sound]`, all 79 modules archived) | No balanced NL244 (`Balanced242No244`), Global Rank-8 Parity Law (`Balanced242Parity`), Anchor-Pair 63/64 Splitting (`Balanced242AnchorPair`), Closed-Form `eminClosed` (`Balanced242SectionBounds`, `Balanced242Farkas`), Shifted All-Degree Multivariate Krawtchouk & Barycenter Laws & Binary Griesmer / Sphere-Packing / `[24,8,≥10]₂` Non-Existence (`Balanced242Centered`), The `t = 98, rank 6, |Z| = 144` normal-form obstruction (`Balanced242T98R6Z144`), Exact `t = 96, (0,31,39)` Mod-16 Walsh Dichotomy (`Balanced242T96Arith`), `t = 96` Quartic Mod-4 Far-Half Law (`Balanced242T96Quartic`), Quartic High-Block Machinery (`Balanced242QuarticHighBlock`), Universal Low-Block Budget & `t = 106` Rank 8 (`Balanced242LowBlock`), Unconditional No Rank-2 (`|Z| = 64`) for `t ≤ 112` & `t = 114, 116` Plane Switch (`Balanced242Z64Switch`), Unconditional Matrix-Free `t = 108, rank 6, |Z| = 112` (`Balanced242T108R6`), Unconditional All `t ≥ 104` Rank 8 (`Balanced242T104R8`), **Unconditional `t = 112` (`Balanced242T112`)**, **Unconditional `t = 114` & `t = 116, k = 12` (`Balanced242T114`)**, **Unconditional Low-Block `t = 118` (`Balanced242T118`)**, and Unconditional `t ≥ 120` (`Balanced242Endpoint`). |
| **Layer B** | **Lean 4.15.0 kernel** + explicit `SectionHypotheses` / `ComputationalClosures` / `EndpointK16Direct` (or `CoveringRadius244`) hypotheses | Coordinate-free `t ≤ 92` exclusion (`Balanced242LowRange`), full 17-profile `t = 94` frontier closure (`Balanced242T94`), centered `t = 96` exclusions for `(21,34,12)`, `(2,47,27)`, `(1,54,24)` (`Balanced242T96Centered`), `(0,51,27)` (`Balanced242T96_0_51_27`), and top-level coordinate-free master theorems **`Balanced242Master.no_balanced_9var_nl242_direct`** (using `EndpointK16Direct` for the sole remaining endpoint case `t = 116, k = 16`) and **`Balanced242Master.no_balanced_9var_nl242`** (using `CoveringRadius244`). |
| **Layer C** | **Independent C++17 / Python exact-arithmetic replay packets** + SHA-256 manifests + positive controls | Finite 7-variable rank-6 section enumerators (`sel`, `sel2`, `sel_e`, `flag_sections`); `t = 96` quartic four-cell enumeration (`nl242_t96_closure.zip`); `t = 98` quartic enumerations + exact integer dual cuts + `2^{21}`-character orbit-mass check (`nl242_t98_closure.zip`); `t = 104–108` middle-window reconstructions (`nl242_middle_closure.zip`); `t ≥ 100` low-block exact rational Farkas/LP duals + zero-LP `RM(3,8)` mod-8 `y_Z` verifiers (`nl242_top_closure.zip`); the direct 114/116 endpoint proof (`nl242_endpoint_closure.zip`, cross-checked by `nl242_endpoint_crosscheck.zip`); and `ρ(1,9) < 244` (Burnside orbit count, class separation, exhaustive search over classes 282/290: `nl244_verify.zip`). |

---

## Theorem Map

See [paper/paper.tex](paper.tex) (Table 2) and `lean/LEAN_PROOF.md` for the theorem-by-theorem cross-reference. The formalization is still being developed, so module counts change between snapshots.

## Acknowledgments & Author's Note

> *Author's note (Daniel Ayomide Shittu):* "Remarkable — after 18 hours pushing balanced 242 to the final frontiers, who would've known it's odd?"

The author thanks AI research and coding assistants — **Antigravity (Google)**, **Claude (Anthropic)**, and **ChatGPT/Codex (OpenAI)** — for assistance with proof exploration, C++/Python enumerator and certificate tooling, Lean 4 formalization, and manuscript preparation. The archived Lean modules are checked by the Lean 4.15.0 kernel with zero external dependencies (`0 sorry`, `0 native_decide`, `0` custom axioms). The finite enumerations are checked by the published C++/Python verifiers, not by Lean. Thanks to Q. Wang, Y. Lou and Z. Wang for the argument behind the `ρ(1,9) < 244` step, and to E. Brier and P. Langevin for their list of cubic forms.

## Citation

<!-- [TODO: Update DOI and arXiv/IACR identifiers after release] -->
```bibtex
@misc{shittu2026nl242,
  author       = {Daniel Ayomide Shittu},
  title        = {No Balanced 9-Variable Boolean Function Has Nonlinearity 242: Spectral-Phase Obstructions, Formalized Exclusions, and Exact Certificates},
  year         = {2026},
  howpublished = {Preprint and Lean 4 formalization},
  note         = {GitHub: [GITHUB_URL], Zenodo DOI: [ZENODO_DOI]}
}
```
