# Lean proofs for t = 86, 88, 90, 92

Lean 4.15.0, no Mathlib. The pair files are self-contained. `Balanced242Section0320.lean` sits on the `build/` library that `../../verify.sh` produces (sat-collapse-lab plus `Balanced242Support`). Nothing uses `sorry`, `native_decide` or extra axioms. Each `#print axioms` line reports only `[propext, Quot.sound]`.

## What is proved

There are two independent pieces.

### 1. The pair-system exclusion (`Balanced242Pair.lean` and the check files)

For t ∈ {86, 88, 90, 92}:

```lean
theorem no_assignment_t (a b c r : Nat) (hT : 6 * a + 3 * b + 5 * c = 8 * t - 480)
    (hr : r ∈ ranks t (a + c)) (x y z : Nat → Nat) (drop : Nat → Bool)
    (hadm : ∀ w < 255, admissible a b c r (x w) (y w) (z w) (drop w) = true)
    (hmom : vsum 255 (fun w => row a b c (x w) (y w) (z w) (drop w)) = rhs a b c r) : False
```

In words, take a global high profile (a,b,c) with the right mass and a global phase rank r allowed by `ranks`. No assignment of a split (x,y,z,drop) to each of the 255 directions works when two conditions hold:

* every split is admissible, meaning both halves pass `half` at rank r, or both at r − 2 when the direction drops the rank;
* the eight sums equal `rhs`. These sums are the direction count, Parseval on the three frequency sets (A², B², C², AB, AC, BC), and the 2^r − 1 rank drops.

The proof has two parts.

* **Generic part (`no_assignment`).** It is proved once for all t. It assumes `rowCheck t a = true` for every a. For each system it takes the stored integer vector v and gets v·rhs < 0 from the check. For every admissible split it gets v·row ≥ 0. Splits with x > a/2 are mapped to their complements with `row_compl` and `admissible_compl`. Summing gives 0 ≤ v·rhs, a contradiction.
* **Finite part (`row_t_a`).** Each one is a single `decide +kernel` over one value of a. It covers every c, every rank in `ranks`, and every split (x, z, y ≡ y₀ mod 8, d). `rows_t` then combines the rows with a `match`.

The admissibility predicate `half` is the complete list of section facts used:

| Condition in `half` | Where it comes from |
|---|---|
| mass ≥ 88, 8 ∣ mass, e ≥ 19 | M ≥ 80 and e ≥ 19 from `check_high_sections` (verify.sh); M = 80 excluded by `more_m80.log`; 8 ∣ M from AGREEMENT_RANGE.md |
| section rank ≤ 6, \|T₇\| ≤ 128·2^{s/2} | AGREEMENT_RANGE.md |
| not (0,32,0) | proved in Lean, piece 2 below |
| `exclAll` (23 profiles), `excl6` (199 rank-six profiles) | `complete 0` / `survivors 0` lines in the sel/sel2 logs |

`gen_lean_data.py` builds the bitsets and certificates by executing `../verify_t86_92.py`'s own fact derivation. So the Lean data and the stdlib replay come from the same parse of the raw logs.

### 2. No (0,32,0) section (`Balanced242Section0320.lean`)

```lean
theorem no_section_0_32_0 (D H : W 7 → Int) (hD : ∀ y, -2 ≤ D y ∧ D y ≤ 2)
    (hspec : ∀ a, transform D a = 2 * H a) (hH : ∀ a, H a = 5 ∨ H a = -5 ∨ H a = 7 ∨ H a = -7)
    (h5 : total 7 (fun a => if H a = 5 ∨ H a = -5 then (1 : Int) else 0) = 32)
    (m : Int) (hm : m = 16 ∨ m = 32 ∨ m = 64 ∨ m = 128)
    (hplat : ∀ y, transform (fun a => phase (H a)) y = 0 ∨ … = m ∨ … = -m) : False
```

This is the hand proof in `../T92_CLOSED.md`, formalized. Parseval gives ΣD² = 172, and duality gives ΣD·q̂ = −1024. Inversion gives 64D = −7q̂ + 12Y. At rank six, each point satisfies 128D² = 8Dq̂ + q̂², and summing gives a contradiction. At rank ≤ 4, 1024D² ≤ 4q̂², which caps ΣD² below 172.

## How to replay

```sh
cd ~/nl242-lab/t92/lean
mkdir -p build
lean -o build/Balanced242PairData.olean Balanced242PairData.lean
LEAN_PATH=build lean -o build/Balanced242Pair.olean Balanced242Pair.lean
LEAN_PATH=build lean Balanced242PairCheck86.lean                         # likewise 88, 90, 92
LEAN_PATH=$HOME/nl242-lab/build lean Balanced242Section0320.lean
```

Measured times (one process each; the Colab logs are in `colab_logs/`):

| t | row theorems | systems | time | peak memory |
|---|---:|---:|---|---|
| 86 | 35 | 4 | 39 s (Mac) | < 1 GB |
| 88 | 38 | 107 | 164 s (Colab) | 0.8 GB |
| 90 | 41 | 188 | 307 s (Colab) | 1.2 GB |
| 92 | 43 | 239 | 439 s (Colab) | 1.7 GB |

Checking a whole t in one `decide` grew to more than 8 GB. Splitting it into one theorem per value of a keeps the kernel's cache small.

## What is not formalized (trust boundary)

1. **The reduction to the pair system.** That a balanced NL-242 function with agreement count t gives a profile, a rank in `ranks`, and admissible splits satisfying `rhs` is the paper argument in AGREEMENT_RANGE.md and T92_CLOSED.md. That covers the high energy identity, the section mass and T₇ facts, the rank-drop count, and the global rank conditions in `rankOK`. Only parts of it are in Lean (`Balanced242Support`, `Balanced242HighSections`).
2. **The enumeration facts.** `excl6` and `exclAll` come from astra's `sel` and from my `sel2` with the MILP for deferred cases. `sel` is not verified. Lean checks only the consequences of these facts.
3. **The plateau property.** That the Walsh transform of a quadratic sign takes values in {0, ±m} is a standard fact. Here it is a hypothesis of `no_section_0_32_0`, not a lemma.
4. **The extremal structure** (U = −σ on supp U when the phase bound is tight) is not used for t ≤ 92 and is not formalized.

## Update 2026-11-22: end-to-end coordinate-free theorems, unconditional no-244, lower-range closure, rank-8 parity & section bounds

All newly proved theorems depend only on `[propext, Quot.sound]` (zero `sorry`, zero `native_decide`, zero `Classical.choice`, except the upper-endpoint `≤ 118` window corollaries that inherit `Balanced242Endpoint.agreement_and_peak_range`).

### Top-level coordinate-free theorems
1. **Unconditional impossibility of balanced nonlinearity ≥ 244 (`Balanced242No244.lean`) — ZERO `SectionEnum`:**
   - `Balanced242No244.no_balanced_nl244`: no balanced 9-variable Boolean function `F : W 9 → Bool` satisfies `∀ a, |booleanSpec F a| ≤ 24`.
   - `Balanced242No244.supportXor_ne_zero_of_cap28` & `peak28_of_cap28`: any balanced `F : W 9 → Bool` with `∀ a, |booleanSpec F a| ≤ 28` automatically satisfies `supportXor F ≠ zero 9` and attains `|booleanSpec F a| = 28` at some mask `a` (removing the `peak` side condition from all coordinate-free theorems).
2. **Coordinate-free exclusion of ALL `t ≤ 92` (`Balanced242LowRange.lean`) — assuming only `SectionEnum`:**
   - `Balanced242LowRange.agreements_ge_86`, `agreements_ge_94`: Parseval on the mass weight `6·1_A + 3·1_B + 5·1_C` excludes `t ≤ 84`, and `Balanced242Complete.no_242_86_to_92` excludes `t ∈ {86, 88, 90, 92}`, giving `94 ≤ agreements f g` (`agreements f g % 2 = 0`).
   - `Balanced242LowRange.axisAgreements_ge_188` & `autocorr_ge_m136` (`[propext, Quot.sound]`): for ANY balanced `F : W 9 → Bool` with `∀ a, |booleanSpec F a| ≤ 28` (no `peak` hypothesis needed), `188 ≤ axisAgreements F` (`4 ∣ axisAgreements F`) and `-136 ≤ autocorr F (supportXor F)` (`8 ∣ autocorr F (supportXor F)`).
   - `Balanced242LowRange.axisAgreements_window_242` & `autocorr_window_242`: combining with `Balanced242Endpoint.agreement_and_peak_range` gives `188 ≤ axisAgreements F ≤ 236` (`-136 ≤ autocorr F (supportXor F) ≤ -40`).
3. **Global rank-8 parity & `t ≥ 94` section-bound machinery (`Balanced242Parity.lean`, `Balanced242Rank8.lean`, `Balanced242SectionBounds.lean`):**
   - `Balanced242Parity.bent_parity`: general symplectic induction on `W (2*m)` proving `∑_x U(x) σ(x) ≡ 2 - 2m (mod 4)` whenever `transform U ≡ 2 (mod 4)` and `transform q = 2^m σ`.
   - `Balanced242Parity.rank8_iff_k_odd` & `rank_eq_8_iff_k_odd`: exact global parity theorem `r = 8 ↔ (pa f g + pc f g) % 2 = 1` (replacing the 3,000-trial numerical check `t94/parity_test.py`).
   - `Balanced242Rank8.rank8_Nplus_formula` & `rank8_secExc_sum`: `2 * Nplus = 3t - 208 - 2k` and `secExc(sec 0) + secExc(sec 1) = Nplus` for every direction `w ≠ 0`.
   - `Balanced242SectionBounds.section_energy`, `section_cs_ok`, `rank6_exc_buckets`: formalizes `4 * ∑ D² = 784 - M`, the general Cauchy–Schwarz dual-flat refinement `mid2.cs_ok` for all section ranks `s ∈ {0, 2, 4, 6}`, and the exact 6-bucket rank-6 `secExc` decomposition backing `rank8filter.emin` and `sel_e`.

### New files (all compiled to `lean/build/*.olean`)
- `Balanced242Plateau`: the plateau property; `(0,b,0) ⇒ b = 80`; the `T7` bound.
- `Balanced242Hyperplane`: hyperplane sections as 7-variable tables.
- `Balanced242Coord`: single F₂-linear involution transvection mapping `(true, 0)` to any nonzero `supportXor F`, proving `supportXor_ne_zero_of_peak28` and `to_adapted`.
- `Balanced242No244`: constructive Reed–Muller residue distance `residue_distance_c`, `diff_spec9_dvd16`, `supportXor_ne_zero_of_cap28`, `no_balanced_nl244`, and `peak28_of_cap28` (all `[propext, Quot.sound]`, zero `SectionEnum`).
- `Balanced242SectionFacts`, `Balanced242Rank`, `Balanced242Global`: global rank structure and `dir_admissible`.
- `Balanced242Final`, `Balanced242RankCond`, `Balanced242Complete`: end-to-end exclusion for `t ∈ {86, 88, 90, 92}`.
- `Balanced242LowRange`: exclusion of `t ≤ 84` and coordinate-free lower-bound/window theorems `axisAgreements_ge_188`, `autocorr_ge_m136`, `axisAgreements_window_242`, `autocorr_window_242`.
- `Balanced242Parity`: symplectic induction `bent_parity` and exact global parity theorem `rank8_iff_k_odd` / `rank_eq_8_iff_k_odd` (`[propext, Quot.sound]`).
- `Balanced242Rank8`: exact rank-8 exception-weight identities `rank8_Nplus_formula` and `rank8_secExc_sum` (`[propext, Quot.sound]`).
- `Balanced242SectionBounds`: `section_energy`, `section_t7_sum`, `section_cs_ok`, and `rank6_exc_buckets` (`[propext, Quot.sound]`).

## Update 2026-11-22 (Part 2): Full kernel-verified Lean 4 closure of all 17 remaining `t = 94` frontier profiles + `(96, 21, 34, 12, 8)`

The entire `t ≥ 94` algebraic/spectral/Krawtchouk/anchor-pair/Farkas engine and all **17 remaining `t = 94` rank-8 frontier profiles** (15 direct Krawtchouk Farkas + 2 layered anchor-pair Farkas covering all 205 anchors) plus the additional `t = 96` profile `(21, 34, 12, 8)` are now compiled to `.olean` and verified directly by Lean 4.15.0's kernel (`decide +kernel`, zero Mathlib, zero `sorry`, zero `native_decide`).

### Algebraic, quartic, Krawtchouk, and Farkas engine modules
1. **`Balanced242AnchorPair.lean` (1,047 lines — all 11 theorems `[propext, Quot.sound]`):**
   - `sec_ell_eq`, `anchor_pair_ranks_63_64` (exact 63 rank-4 / 64 rank-6 anchor-pair subsection split for any rank-8 half),
   - `six_section_energy`, `six_section_div4`, `six_section_jensen` (exact 6-variable Jensen admissibility bound for `r ∈ {4, 6}`),
   - Explicit degree-2 and degree-4 Krawtchouk identities/inequalities `kraw_deg2_200`, `kraw_deg2_110`, `kraw_deg4_400`, `kraw_deg4_310`, `kraw_deg4_220`, `kraw_deg4_211`.
2. **`Balanced242Quartic.lean` (828 lines — all 8 theorems `[propext, Quot.sound]`, zero `SectionEnum`):**
   - Unconditional proofs of all quartic weight & divisibility bounds in `replay.py`'s `six` and `half`:
     `half_mass_div8` (`8 ∣ 6x + 3y + 5z`), `flat4_exc35_odd`, `flat5_exc35_even`, `flat5_rank4_exc35`,
     `six_bc_ge_4` (`4 ≤ b + c` at 6-var rank 4), `six_bc_ge_8` (`8 ≤ b + c` at 6-var rank 6 via constructive finite pigeonhole),
     `half_yz_ge_8` (`8 ≤ y + z` at 7-var rank 4), `half_yz_ge_16` (`16 ≤ y + z` at 7-var rank 6).
3. **`Balanced242Krawtchouk.lean` (675 lines — all 7 theorems `[propext, Quot.sound]`):**
   - All-degree multivariate Krawtchouk theory for all `n : Nat` and all `(i, j, l) : Nat³`:
     `kraw_eq_krawRec`, `kraw_at_zero`, `kraw_flip`, `sum_triple_esym`,
     `kraw_triple_nonneg_and_mod` (simultaneously proves `-C(a,i)C(b,j)C(c,l) ≤ ∑_{v≠0} K_i K_j K_l` and `2^n ∣ (∑ + dc)`),
     `kraw_even_flip`, `kraw_triple_deg2_eq` (all six degree-2 Parseval equalities for pairwise disjoint `P, Q, R`).
4. **`Balanced242Farkas.lean` (2,035 lines — zero `sorry`, zero `native_decide`):**
   - `eminClosed_le_secExc` (`[propext, Quot.sound]`): closed-form lower bound `eminClosed M k ≤ secExc`, matching `rank8filter.emin` identically on all 3,943 half-sections across all 18 `t = 94 / 96` profiles.
   - `quarter_hyperplane_counts` (`[propext, Quot.sound]`): 2-plane four-quarter coupling (`liftPt 7 w v` and `add 8 w (liftPt 7 w v)`).
   - `farkas_refute` & `affine_cert_refute` (`[propext, Quot.sound]`): generic exact-integer Farkas refutation and sparse all-degree Krawtchouk certificate soundness (using proved-equivalent $O(k)$ `chooseFast` / `krawFast`).
   - `section_costR6_le`, `sixOK_of_subsection`, `cond_cert_refute`, and master theorem `exclude_rank8_profile` (`[propext, Classical.choice, Quot.sound]`): end-to-end refutation of real `(f, g : Half)` from arbitrary anchor-pair peeling layers + final Krawtchouk Farkas certificate under `SectionEnumE excl6Mask eBounds`.
5. **`Balanced242FastCond.lean` (674 lines — zero `sorry`, zero `native_decide`):**
   - Pure primitive-`Nat` / `match`-only kernel-fast anchor-pair verifier (`checkLayerFast2`) proved sound by direct implication `checkLayerWithMask_of_fast2` into `Balanced242Farkas.checkLayerWithMask` (~17× faster subtype enumeration; ~1 GB peak RAM with 1-anchor-per-theorem chunking).

### Kernel-checked `t = 94` (+ extra `t = 96`) certificate modules
- **`Balanced242T94Data.lean`**: generated by `gen_t94_lean.py` from `t94/t94_anchor_pair_certs.json` + `frontier_input.json` (252 distinct excluded rank-6 sections in bitmask `excl6MaskT94`, 59 `sel_e` bounds `eBoundsT94`, 16 direct sparse Krawtchouk certificates, and 205 anchor-pair certificates).
- **`Balanced242T94Direct.lean`**: kernel-verified exclusion of all **15 direct `t = 94` frontier profiles** (`(0,29,37)` through `(17,30,16)`) plus **`(96, 21, 34, 12, 8)`**.
- **`Balanced242T94L12_base`, `Balanced242T94L12_c0..c7`, `Balanced242T94L15_base`, `Balanced242T94L15_c0..c6`, `Balanced242T94Layered.lean`**: kernel-verified 1-layer anchor-pair exclusion of **`(94, 12, 25, 25, 8)`** (108 anchors) and **`(94, 15, 24, 22, 8)`** (97 anchors).
- **`Balanced242T94.lean`**: master theorem **`Balanced242T94.t94_all_17_frontier_excluded`** (`[propext, Classical.choice, Quot.sound]`) excluding all 17 remaining `t = 94` rank-8 frontier profiles from `remaining_profiles.tsv`, plus **`Balanced242T94.t96_21_34_12_excluded`**.

## Part 3: `t = 96` & `t = 98` formalization (7 new modules — 68 modules total)

1. **`Balanced242T98R6Z144.lean`** (**UNCONDITIONAL**, zero `SectionEnum`, `[propext, Classical.choice, Quot.sound]`):
   - **`Balanced242T98R6Z144.no_t98_r6_z144`** excludes the rank-6, `|Z| = 144` normal form at `t = 98`. Its inputs include a weight-28 bent function `Q6` and the Walsh residue pattern `hZ_pat` in the chosen coordinates. The master theorem calls `t98_remaining` for this value of `|Z|`.
   - Tightens a subtle step in Step 3 of the hand proof: rather than isolating a single fiber indicator $\mathbf{1}_{F_x}$ by linear combinations, proves it strictly via pairwise XORs $p_i \oplus p_j = \mathbf{1}_{F_i \sqcup F_j}$ (which are `Cube`), the `RM(2, 6)` weight theorem (`rm2_6_weight`: weights $\in \{0,16,24,28,32,36,40,48,64\}$), and the arithmetic lemma forcing one fiber of size 28 and three of size 0.
2. **`Balanced242Centered.lean`** (**general `t = 96 / 98` mathematical engine**, 15 exported theorems, zero `SectionEnum`):
   - All-degree **shifted multivariate Krawtchouk** theorem (`sum_triple_esym_shifted`, `kraw_triple_shifted_nonneg_and_mod`, `kraw_triple_shifted_deg1_eq`).
   - **Barycenter / marker-center** translation & puncturing invariants (`halfCnt_mod2_eq_dot_barycenter`, `barycenter_translate_odd`, `cut_sum_eq_half`) matching `rank8cp/center96.py`.
   - Exact **residual kernel coupling** (`residual_kernel_counts`), the general binary **Griesmer bound** (`griesmer_bound`), the **sphere-packing bound** for distance ≥ 3 (`sphere_packing_d3`), and the unconditional coding-theory impossibility **`no_binary_code_24_8_10`** (no binary linear `[24, 8, ≥10]_2` code exists: `g(8,11) = 26 > 24`, `g(7,6) = 15 > 14`, `2^6 (1+9) = 640 > 512`).
   - Verified Farkas engines & full profile bridges: `centered_cert_refute`, `bary_cert_refute`, `origin_pin_refute`, `residual_cert_refute`, `origin_pin_residual_24_refute`.
3. **`Balanced242T96Arith.lean`** (**UNCONDITIONAL**, zero `SectionEnum`):
   - `t96_0_31_39_walsh_energy`, `t96_0_31_39_small_C` (`[propext, Quot.sound]`), and **`t96_0_31_39_dichotomy`** (`[propext, Classical.choice, Quot.sound]`): formalizes the exact Walsh mod-16 energy & Parseval dichotomy for `t = 96, (0, 31, 39)` (`t96/check_03139.py`): `|W_{B-C}(w)| ≤ 40`, splitting cleanly into the unique-40 branch (automatically realizing a `c ≤ 16` side with `|2(b-c)+8| = 40`) vs the cap-24 branch (Parseval on `clsC` forcing a `c ≤ 16` side with `|2(b-c)+8| ≤ 24`).
4. **`Balanced242T96Data.lean`, `Balanced242T96_2_47_27_L0.lean`, `Balanced242T96_1_54_24_L0.lean`, `Balanced242T96Centered.lean`** (`[propext, Classical.choice, Quot.sound]`):
   - **`Balanced242T96Centered.excl_96_2_47_27`**: kernel-verifies all 10 layer-0 anchor-pair certs + the 10-term origin-pinned centered Krawtchouk Farkas cert excluding `(96, 2, 47, 27, 8)` modulo `SectionEnumE excl6MaskT96 eBoundsT96` and the single flag leaf `(0, 26, 10)`.
   - **`Balanced242T96Centered.excl_96_1_54_24`**: kernel-verifies all 20 layer-0 anchor-pair certs + both 8-term 7D residual Krawtchouk Farkas certs `(0, 46, 6)` and `(0, 48, 8)` + unconditional `no_binary_code_24_8_10`, excluding `(96, 1, 54, 24, 8)` modulo `SectionEnumE excl6MaskT96 eBoundsT96` and the 3 flag leaves `(0, 44, 4), (0, 38, 6), (0, 40, 8)`.

### Colab / standalone replay
`nl242_lean_colab.tar.gz` + `verify_nl242_colab.ipynb` package all **79** zero-Mathlib Lean 4.15.0 source modules (`sat-collapse-lab` base + `nl242-lab` base + `t92/lean`) with a strictly sequential low-RAM (`~1–1.7 GB` peak RSS) replay script `nl242_lean/replay_all.sh`.

## Part 4: Full `t = 96..118` Formalization & Top-Level Master Theorem (11 new modules — 79 modules total)

All 11 new modules compile cleanly to `build/*.olean` with zero Mathlib, zero `sorry`, zero `native_decide`, and zero custom axioms:

69. **`Balanced242T96Quartic.lean`** (**UNCONDITIONAL**, `[propext, Quot.sound]`):
    - `rank8_sec_rr_eq_2`, `rank8_half_mod_laws`, `rank8_barycenters_paired`, `rank8_a0_far_yz_div4` (exact mod-4 far-half parity law for `a = 0` rank-8 profiles), and `no_section_yz_eq_18`.
70. **`Balanced242T96_0_51_27.lean`** (`[propext, Classical.choice, Quot.sound]`):
    - **`Balanced242T96_0_51_27.excl_96_0_51_27`**: closes the second `b + c = 78` profile at `t = 96`, `(0, 51, 27)`, using `rank8_a0_far_yz_div4` and three tiny centered integer Farkas certificates (6, 5, 5 terms), with zero flag leaves and zero anchor peeling (`SectionEnumE excl6MaskT96 []` only).
71. **`Balanced242QuarticHighBlock.lean`** (**UNCONDITIONAL**, `[propext, Quot.sound]`):
    - Exact rank-8 high-block inversion `2 K D = 28 - 3 S + 32 u`, ternary counts `2p = 3t - 208 - 2(a + c)`, first-moment identity `⟨u, S⟩ = 10(b + c) - 16 c`, all three hinge lower bounds `(h, l) ∈ {(14, 6), (18, 6), (18, 10)}`, and exact integer dual-cut soundness.
72. **`Balanced242LowBlock.lean`** (**UNCONDITIONAL**)
    - Universal low-block defect budget `4(n_0 + 2n_8) = 2304 - 5|Z| - 16t`, autocorrelation congruence mod 32, complete rank-vs-`|Z|` classification (`rank_Zc_values`), all budget exclusions (`no_Zc_{256,160,144,136,128,120,112,96}_of_t_ge_*`), `t_ge_114_forces_Z64`, `no_t106_rank8`, and `t108_rank6_D_eq_rad`.
    - The budget, autocorrelation congruence, rank classification, individual budget exclusions and `no_t106_rank8` use `[propext, Quot.sound]`. The conclusions `t_ge_114_forces_Z64` and `t108_rank6_D_eq_rad` also use `Classical.choice`.
73. **`Balanced242Z64Switch.lean`** (the `t ≤ 112` exclusion and switch construction are **unconditional**)
    - `z64_small_masks_ge_9`, **`no_Z64_of_t_le_112`** (unconditionally excludes ALL of rank 2 `rr = 64` for every `t ≤ 112`), `t112_forces_rank4_Z96`, `endpoint_switched_blocks`, `z64_plane_switch_114_116`, and `no_t114_t116_of_covering_radius` (under `CoveringRadius244`).
    - The small-mask bound and `no_Z64_of_t_le_112` use `[propext, Quot.sound]`. The other four theorems listed here also use `Classical.choice`.
74. **`Balanced242T108R6.lean`** (**UNCONDITIONAL**)
    - `cube8_weight_cases`, `affine8_weight_cases`, and **`Balanced242T108R6.no_t108_rank6`** (matrix-free exclusion of `t = 108`, rank 6, `|Z| = 112` via quadratic weight gaps on `W 8` forcing `144² = 20736 > 16384`).
    - Both weight lemmas use `[propext, Quot.sound]`. The exclusion `no_t108_rank6` also uses `Classical.choice`.
75. **`Balanced242T104R8.lean`** (**UNCONDITIONAL**, `[propext, Quot.sound]`):
    - **`Balanced242T104R8.no_t104_rank8`** and **`Balanced242T104R8.no_rank8_of_t_ge_104`**: unconditionally excludes ALL rank-8 (`rr = 1`) tables for every even `t ≥ 104`!
76. **`Balanced242T112.lean`** (**100% UNCONDITIONAL**, zero LP, zero `SectionEnum`, zero `CoveringRadius244`; `no_t112` uses `[propext, Classical.choice, Quot.sound]`):
    - `rank4_Z96_zero_moments`, **`rank4_Z96_n0_ge8`**, `rank4_Z96_n0_eq8_subspace` (`[propext, Quot.sound]`), 4-stage butterfly FWHT kernel check over all 729 ternary 4-bit cells (`checkAll729Fast_ok`), symplectic decomposition (`rank4_Z96_symplectic_decomp`), and **`Balanced242T112.no_t112`** (complete unconditional exclusion of `t = 112` across all ranks!).
77. **`Balanced242T114.lean`** (**100% UNCONDITIONAL**, zero `SectionEnum`, zero `CoveringRadius244`; `[propext, Classical.choice, Quot.sound]`):
    - **`Balanced242T114.no_t114`**: unconditionally excludes `t = 114` via `Balanced242Sectors.halfspace_small_counts` and the `[12, 9, 4]` Hamming sphere-packing contradiction `512 * 13 = 6656 > 4096 = 2¹²`.
    - **`Balanced242T114.t116_forces_k16`**: unconditionally excludes the `k = 12` branch of `t = 116`, shrinking the ENTIRE endpoint residual to the single case `t = 116, k = 16`.
78. **`Balanced242T118.lean`** (**100% UNCONDITIONAL**, low-block-only, zero `hi`, zero `SectionEnum`, zero `CoveringRadius244`; `[propext, Classical.choice, Quot.sound]`):
    - **`Balanced242T118.no_t118`**: unconditionally excludes `t = 118` via continuation-passing RREF affine-subspace enumeration (`rrefAll`) + precomputed shifted-`Nat` binary-tree kernel checks (`check_222_ok`, `check_133_ok`, `check_044_ok` with empty-cell integer rounding, `check_224_ok`), formalizing `check_t118.py` directly inside Lean's kernel.
79. **`Balanced242Master.lean`** (both exclusion theorems use `[propext, Classical.choice, Quot.sound]`):
    - `endpointK16_of_coveringRadius : CoveringRadius244 → EndpointK16Direct` (`[propext, Quot.sound]`).
    - **`Balanced242Master.no_balanced_9var_nl242_direct`**: top-level coordinate-free exclusion of ALL balanced 9-variable NL-242 Boolean functions across all even `t ∈ [0, 256]`, using `SectionHypotheses` (Layer B), `ComputationalClosures` (Layer C for `t ∈ {94..110}`), and `EndpointK16Direct` (`t = 116, k = 16`, ZERO `CoveringRadius244`).
    - **`Balanced242Master.no_balanced_9var_nl242`**: same coordinate-free master theorem discharging `EndpointK16Direct` via `CoveringRadius244` (`nl244_verify.zip`).

Remaining trust boundary (explicitly parameterized in `Balanced242Master`):
1. `SectionHypotheses` (`SectionEnum` / `SectionEnumE`): finite 7-variable rank-6 section enumerations (`sel`, `sel2`, `sel_e`).
2. `ComputationalClosures`: the large-search computational closures for `t ∈ {94 (non-frontier), 96, 98, 100, 102}` and `t ∈ {104, 106}` (`r ∈ {4, 6}`) and `t ∈ {108, 110}` (`r = 4, Z = 96`), each backed by a SHA-256-manifested replay packet (`nl242_t96_closure.zip`, `nl242_t98_closure.zip`, `nl242_middle_closure.zip`, `nl242_top_closure.zip`).
3. Sole remaining endpoint case `t = 116, k = 16`: discharged EITHER by `EndpointK16Direct` (`nl242_endpoint_closure.zip`, independently cross-checked by `nl242_endpoint_crosscheck.zip`) OR by `CoveringRadius244` (`nl244_verify.zip`).

Everything else — coordinate-free `no_balanced_nl244` / `peak28_of_cap28`, `Balanced242Parity`, `Balanced242SectionBounds`, `Balanced242AnchorPair`, `Balanced242Quartic`, `Balanced242Krawtchouk`, `Balanced242Centered`, `Balanced242T96Arith`, `Balanced242T96Quartic`, `Balanced242QuarticHighBlock`, `Balanced242T98R6Z144`, `Balanced242LowBlock`, `Balanced242Z64Switch` (no `r=2` for `t ≤ 112`), `Balanced242T108R6`, `Balanced242T104R8`, **`Balanced242T112`**, **`Balanced242T114`** (`t = 114` & `t = 116, k = 12`), **`Balanced242T118`**, and `t ≥ 120` — is proved **100% unconditionally inside the Lean 4.15.0 kernel** with zero external hypotheses.

### Replay audit of the master hypotheses (2026-11-22)

The direct master theorem takes three section-enumeration claims, nine residual exclusions, and one endpoint exclusion. All seven release ZIPs match the release manifest, and all 338 entries in their internal manifests match (`nl242_top_closure.zip` was repacked to 104 SHA-256-verified files including `t100/z128/verify_z128_reductions.cpp`, `t100/z112/check_small_masks.cpp`, and `t100/z112/verify_z112_all45_exact.cpp`). The checks below distinguish a replay of a finite search from a proof that its inputs cover every candidate allowed by the Lean statement.

| Input to the master theorem | Evidence checked |
| --- | --- |
| `enum7`, `enum94`, `enum96` | The section checker excluded deficit at most 72 and at most 18 exceptions. All 20 remaining mass-80 profiles have completed zero-hit logs. Decoding the Lean constants gave 23 all-rank exclusions, 199 rank-6 exclusions for `enum7`, 252 distinct profiles for `enum94`, and 242 for `enum96`. The 59 `enum94` lower bounds matched the recorded searches. For the shared profile `(1,39,1)`, the integer sign-extension replay checked all 3,360 deferred rows and found zero extensions. This audit matched the stored section logs and reran the deferred checks. |
| `t94_nonfrontier` | The middle verifier regenerated the 35 starting profiles. The exact raw replay eliminated 18, leaving precisely the 17 rank-8 profiles in the Lean frontier. The anchor-pair replay also excluded all 17. |
| `t96_remaining` | The same upstream replay reproduced the 55 remaining rank-8 profiles. The quartic checker eliminated all 55, including the two weight-78 profiles. |
| `t98_remaining` | The rank-6 replay excluded all 22 remaining profiles. The earlier certificates and quartic coverage checks account for the 102 rank-8 profiles. The direct checker re-evaluated 92,450 and 8,024 support/profile pairs at weights 78 and 82. The accelerated enumeration was checked against archived jobs. |
| `t100_remaining` | **Previously identified universal rank-6 reduction issue RESOLVED.** The repacked top packet's quick checks (`verify_quick.sh`, 10/10 steps) pass. For `Zc = 128`, Section 5 of `paper/t100.tex` proves the full case-tree reduction (including hand closures of Branches II-B2 and II-B3 via Lemma 5.4 and Proposition 5.5, the symplectic-trace proof in Lemma 5.3 excluding `(2, 6, 2)` on all 315 isotropic rank-2 forms, and the exact `GL(8, 2)` shear exchanging the two 2,880-element `(6, 6)` orbits). For the two Branch-I weight-16 orbits (where the uncoupled general solver `solve_branchI_rest` reported 589,824 joins each while `solve_branchI_wt16_fast` reported 0), **Lemma 5.2 (`lem:wt16`)** of `paper/t100.tex` proves the global `64x` normalization `p'_{00}|_H = p'_{00}|_{H^c}`, the `p'_{01}|_H` half-completion condition (`has_L0_any`), and the 22-bit degree-4–6 subcube syndrome on `A = z_{00} + z_{10}`; line-by-line code verification (`verify_z128_reductions.cpp`, Pass 5) confirms bit-for-bit agreement with `solve_branchI_wt16_fast.cpp` (64/64 admissible local tuples match lines 220–228 modulo 16, `opts_L0` `H <-> H^c` symmetry is exact, `|H^c ∩ U| = |H ∩ U| = 8`, all 65,536 normalized `p5` and `po` in `RM(2, 5)` are tested, and the 22-bit subcube positive control passes). For `Zc = 112`, Proposition 5.6 (`Balanced242Plateau.section_0_b_0` + `check_small_masks.cpp`) proves `0 <= h <= 16` even (45 pairs `(h, p)`), Lemma 5.7 proves the 1-WHT mod-3 extension identity, Lemma 5.8 classifies all three `β_U` types, (R1) proves `(h, p) = (0, 0)` unconditionally by hand (`m_2 >= 16 > 10`), and `verify_z112_all45_exact.cpp` (7/7 positive controls passing) excludes all 111/111 live cases with 0 survivors, closing three omissions found in the legacy `t100/z112/` scripts. |
| `t102_remaining` | Replayed the rank-8 and rank-6 `Zc = 128` checks and checked the low-rank profile certificates. The rank-6 `Zc = 112` branch has separate programs in the top packet. A fresh replay of that entire branch was outside this audit. |
| `t104_r4_r6`, `t106_r4_r6`, `t108_r4_Z96`, `t110_r4_Z96` | Replayed the middle rank-4 filters, rank-6 checks at 104 and 106, the rank-4 reconstruction and transversal checks at 108, and the 110 verifier with its 279 integer Farkas certificates. |
| `EndpointK16Direct` | The direct endpoint verifier and a separate implementation both excluded the low complement. The covering-radius alternative is unnecessary for this route. |

**Audit resolution (2026-11-22):** The previously identified universal rank-6 reduction issue at `t = 100` — specifically the Branch-I weight-16 normalization, half-completion, and 22-bit syndrome restrictions — is **resolved** by **Lemma 5.2 (`lem:wt16`)** and Section 5 of [paper/t100.tex](../../paper/t100.tex), with programmatic code-vs-math verification in `t100/z128/verify_z128_reductions.cpp` (Passes 1–5) and full 45-pair $|Z|=112$ verification in `t100/z112/verify_z112_all45_exact.cpp` inside the repacked `nl242_top_closure.zip`. Every Layer-C hypothesis of `Balanced242Master.no_balanced_9var_nl242_direct` is now backed by written reductions and SHA-256-manifested replay packets.
