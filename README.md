# MiyaokaMori-CharZero

A Lean 4 formalization, over Mathlib, of the algebraic proof of the **Miyaoka–Mori criterion** in characteristic zero given in

> Bin Dong, Guoxiong Gao, Bin Guo, Zeming Sun, Bin Wu and Song-Yan Xie, *Constructing Rational Curves via Jets on Projective Varieties with Non-Nef Canonical Bundle*, 2026, [arXiv:2609.28465](https://arxiv.org/abs/2609.28465).

## The mathematics

Let `k` be an algebraically closed field of characteristic zero, `X` a smooth projective variety over `k`, and `f : C → X` a nonconstant morphism from a smooth connected projective curve. If `−K_X · f_*[C] > 0`, then through every closed point of `f(C)` there is a rational curve: a nonconstant morphism `b : ℙ¹ → X` with `b(0) = x`.

The proof was found by the automated reasoning system Pharos and rewritten by the human authors. This repository formalizes the main theorem together with the key steps of its method, so that it certifies the method of the paper and not only its conclusion. Every result below is proved with no `sorry`, and depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 1.1 (Miyaoka–Mori) | `miyaoka_mori` | `MiyaokaMori/Targets/MainTheorem.lean` |
| Proposition 2.4 (The weighted intersection) | `harmonic_intersection` | `MiyaokaMori/Targets/HarmonicIntersection.lean` |
| Lemma 2.5 (A negative horizontal curve) | `negative_horizontal` | `MiyaokaMori/Targets/NegativeHorizontalCurve.lean` |
| Lemma 3.1 (An affine lift after finite base change) | `affine_lift_after_base_change` | `MiyaokaMori/Targets/AffineLiftAfterBaseChange.lean` |
| Proposition 3.2 (Realization of the inverse tautological class) | `inverse_tautological_class` | `MiyaokaMori/Targets/InverseTautologicalClass.lean` |
| Lemma 4.1 (Coefficient vanishing and nonconstant projection) | `realization_coefficients` | `MiyaokaMori/Targets/RealizationCoefficients.lean` |
| Theorem 4.2 (Polynomial realization), with Corollary 4.3 (Ruled-surface realization) | `realization` | `MiyaokaMori/Targets/Realization.lean` |
| Lemma 5.1 (Prescribed-point specialization) | `prescribed_point_specialization` | `MiyaokaMori/Targets/PrescribedPointSpecialization.lean` |
| The identity `−K_X · f_*[C] = deg f^*T_X` (Section 2) | `degree_identity` | `MiyaokaMori/Paper/S1Intro/DegreeIdentity.lean` |

The library is organized by topic: `MiyaokaMori/Paper/` holds the arguments specific to the paper, while `AlgebraicGeometry/`, `RingTheory/`, `Algebra/` and `CategoryTheory/` hold the general theory the proof needs and Mathlib does not yet provide.

## SHEAF

The formalization was produced by **SHEAF** (Scalable Hierarchical Engine for Autonomous Formalization), a system of autonomous agents that unfolds a paper into a dependency graph of statements, formalizes the statements first, and then proves them while pruning every part of the graph that the formal proof does not need. SHEAF will be released at <https://github.com/frenzymath/SHEAF>.

## Checking the results with Lean comparator

The results above have been checked with [Lean comparator](https://github.com/leanprover/comparator), which verifies in a sandbox that each theorem proves exactly the statement given in a separate challenge file and uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
To repeat the check, install comparator's dependencies (`landrun` and a `lean4export` matching this toolchain), fetch the Mathlib cache with `lake exe cache get`, and run `lake env <path/to/comparator> comparator.json` from the repository root; the challenge statements are in `Challenge.lean` and the configuration in `comparator.json`.

## Building

Lean `v4.33.1` and Mathlib at commit `0df444a` (pinned in `lean-toolchain` and `lake-manifest.json`).

```bash
lake exe cache get
lake build
```
