import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.LineBundleDifferenceOfEffective
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedSubschemeProperOver
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOfClosedSubscheme
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOpCapProdAlgebra
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDimensionAndFrame
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperEqChowZeroDim
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleEqPushforward
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperIntersectionTrivialFactor
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0ber
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0beu

/-! # The projective inductive step of Snapper = Chow

Fix a field `k` and `d`, and assume `P(k, d)` ("`χ`-intersection number = Chow intersection number" in
dimension `d`, for all `d`-dimensional locally Noetherian schemes projective over `k`). Then for an
integral scheme `X` of dimension `d+1` projective over `k` and any `d+1` invertible sheaves `L_0, …, L_d`,
`(L_0⋯L_d·X)_χ = deg(c_1(L_0) ∩ ⋯ ∩ c_1(L_d) ∩ [X]_{d+1})`.

Proof:
1. Both sides are additive in `L_0` and depend only on its isomorphism class: on the left by Stacks 0BER
   (the intersection number is additive when `L_0 ≅ L'⊗L''`; taking `L'' = O_X` and `O ≅ O⊗O` gives
   `(O·L_1⋯) = 0`, hence invariance under isomorphism and `(L'^∨·…) = −(L'·…)`); on the right
   `c_1(L'⊗L'') = c_1(L') + c_1(L'')`, `c_1(O_X) = 0` and invariance under isomorphism
   (`firstChernClass_one` / `firstChernClass_congr`), and `capProd` is linear in each factor.
2. `X` integral and projective, so `L_0 ≅ O(A) ⊗ O(B)^∨` with `A`, `B` effective Cartier divisors
   (Stacks 0AYM). By step 1 it suffices to treat `L_0 ≅ O(D)` with `D` an effective Cartier divisor.
3. `D = ∅` (`O(D) ≅ O_X`): both sides are `0` (step 1). Assume `D ≠ ∅`; `X` is integral of dimension
   `d+1` and of finite type over a field, so every component of `D` has dimension `d` (Krull's principal
   ideal theorem + 0A21), `dim D = d`, and `D` is proper over `k` (closed immersion) and locally Noetherian.
4. Left side: Stacks 0BEU gives `(L_0⋯L_d·X) = (L_1|_D⋯L_d|_D·D)`.
5. Right side: `capProd` is independent of the order of the factors (`RatDivisorOp.capProd_comm`), so
   `c_1(L_0)` may act first on `[X]_{d+1}`. The canonical section `1_D` of `O(D)` is nonzero with zero
   ideal `I_D` (`EffectiveCartierDivisor.canonicalSection`), and
   `EffectiveCartierDivisor.firstChernClass_cap_fundamentalChowClass` gives
   `c_1(O(D)) ∩ [X]_{d+1} = [D]_d = ι_*[D]_d` (definition of `IdealSheafData.cycle`). Then the projection
   formula (`chowPushforward_firstChernClass_pullback`, `d` times):
   `c_1(L_1) ∩ ⋯ ∩ c_1(L_d) ∩ ι_*[D]_d = ι_*(c_1(L_1|_D) ∩ ⋯ ∩ c_1(L_d|_D) ∩ [D]_d)`, and the degree is
   compatible with the pushforward.
6. Apply `P(k, d)` to `D` and `L_i|_D` (`i = 1..d`); both sides agree.

Source: the second half of the proof of Stacks 0BFI (0AYM, 0BER, 02SP, 0BEU, 02SQ).

The purely algebraic Chow-side lemmas (moving out the factor `0`, `RatDivisorOp.capProd_succ`; additivity
of `ratDivisorOpOfLineBundle`; the projection formula for cap products) are in
`RatDivisorOpCapProdAlgebra.lean`; the two geometric facts about `D` (`D ≠ ∅ ⇒ dim D = d`;
`D = ∅ ⇒ O(D) ≅ O_X`) are in `SnapperEqChowProjectiveStepDivisor`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Replacing one member of a family of line bundles by a line bundle gives a family of line bundles. -/
theorem isLineBundle_update {X : Scheme.{u}} {d : ℕ} (L : Fin d → X.Modules)
    [∀ i, (L i).IsLineBundle] (i : Fin d) (M : X.Modules) [M.IsLineBundle] :
    ∀ j, (Function.update L i M j).IsLineBundle := by
  intro j
  by_cases h : j = i
  · subst h; simpa using (inferInstance : M.IsLineBundle)
  · simpa [Function.update_of_ne h] using (inferInstance : (L j).IsLineBundle)

/-- `h ▸ z` is the index cast `ChowGroupRat.congr`. -/
theorem ChowGroupRat.eqRec_eq_congr {X : Scheme.{u}} {p q : ℕ} (h : p = q) (z : ChowGroupRat X p) :
    (h ▸ z : ChowGroupRat X q) = ChowGroupRat.congr X h z := by
  subst h; rfl

/-- `snapperIntersection` only depends on the family (the line-bundle instances are proofs). -/
theorem snapperIntersection_congr_fun {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X) {d : ℕ} (hd : X.dimension = d)
    (L L' : Fin d → X.Modules) [∀ i, (L i).IsLineBundle] [∀ i, (L' i).IsLineBundle] (h : L = L') :
    snapperIntersection X hX hd L = snapperIntersection X hX hd L' := by
  subst h; rfl

/-- The Chow side, as a linear map in the class `E ∩ [X]_{d+1}` sitting in the slot of `L 0`:
`Θ(β) = deg (c_1(L_1) ∩ ⋯ ∩ c_1(L_d) ∩ β)`. -/
def chowSideMap {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) [IsLocallyNoetherian X] {d : ℕ} (L : Fin (d + 1) → X.Modules)
    [∀ i, (L i).IsLineBundle] : ChowGroupRat X d →ₗ[ℚ] ℚ :=
  ChowGroupRat.degree X hX ∘ₗ
    RatDivisorOp.capProd (fun i : Fin d => ratDivisorOpOfLineBundle (L i.succ)) 0 ∘ₗ
      ChowGroupRat.congr X (by simp)

/-- The Chow side as a function of the operator `E` in the slot of `L 0`:
`Ψ(E) = deg (c_1(L_1) ∩ ⋯ ∩ c_1(L_d) ∩ (E ∩ [X]_{d+1}))`. It is additive in `E`. -/
def chowSideFunctional {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) [IsLocallyNoetherian X] {d : ℕ} (L : Fin (d + 1) → X.Modules)
    [∀ i, (L i).IsLineBundle] (E : RatDivisorOp X) : ℚ :=
  chowSideMap X hX L (E d ((1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass (d + 1)))

theorem chowSideFunctional_def {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X) [IsLocallyNoetherian X] {d : ℕ}
    (L : Fin (d + 1) → X.Modules) [∀ i, (L i).IsLineBundle] (E : RatDivisorOp X) :
    chowSideFunctional X hX L E
      = ChowGroupRat.degree X hX
          (RatDivisorOp.capProd (fun i : Fin d => ratDivisorOpOfLineBundle (L i.succ)) 0
            (ChowGroupRat.congr X (by simp)
              (E d ((1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass (d + 1))))) := rfl

theorem chowSideFunctional_add {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X) [IsLocallyNoetherian X] {d : ℕ}
    (L : Fin (d + 1) → X.Modules) [∀ i, (L i).IsLineBundle] (E E' : RatDivisorOp X) :
    chowSideFunctional X hX L (E + E') = chowSideFunctional X hX L E + chowSideFunctional X hX L E' :=
  map_add (chowSideMap X hX L) (E d ((1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass (d + 1)))
    (E' d ((1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass (d + 1)))

theorem chowSideFunctional_zero {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X) [IsLocallyNoetherian X] {d : ℕ}
    (L : Fin (d + 1) → X.Modules) [∀ i, (L i).IsLineBundle] :
    chowSideFunctional X hX L 0 = 0 :=
  map_zero (chowSideMap X hX L)

/-- Step 5 (first half): the right-hand side of `SnapperEqChowFor` is `Ψ(c_1(L_0))`
(commutativity of caps in the form `RatDivisorOp.capProd_succ`). -/
theorem chowSide_eq_chowSideFunctional {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X) [IsLocallyNoetherian X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] {d : ℕ}
    (L : Fin (d + 1) → X.Modules) [∀ i, (L i).IsLineBundle] :
    ChowGroupRat.degree X hX
        (RatDivisorOp.capProd (fun i => ratDivisorOpOfLineBundle (L i)) 0
          ((by simp : d + 1 = 0 + Fintype.card (Fin (d + 1))) ▸
            ((1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass (d + 1))))
      = chowSideFunctional X hX L (ratDivisorOpOfLineBundle (L 0)) := by
  rw [chowSideFunctional_def]
  obtain ⟨z, hz⟩ : ∃ z : ChowGroupRat X (d + 1),
      (1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass (d + 1) = z := ⟨_, rfl⟩
  rw [hz]
  have e₁ : d + 1 = 0 + d + 1 := by omega
  rw [ChowGroupRat.eqRec_eq_congr,
    ← ChowGroupRat.congr_trans e₁ (by simp : 0 + d + 1 = 0 + Fintype.card (Fin (d + 1))),
    RatDivisorOp.capProd_succ (k := k) (fun i => ratDivisorOpOfLineBundle (L i))
      (fun j => ratDivisorOpOfLineBundle_mem_lineBundleSpan (L j)) 0 _ (by simp) _,
    RatDivisorOp.apply_congr (ratDivisorOpOfLineBundle (L 0)) (by omega : d = 0 + d) e₁,
    ChowGroupRat.congr_trans]
  rfl

/-- Steps 3–6 for `L_0 = O_X(D)`, `D` an effective Cartier divisor: both sides agree.
`D = ∅`: both sides vanish (`snapperIntersection_eq_zero_of_iso_unit`, `c_1(O_X) = 0`).
`D ≠ ∅`: `dim D = d`; left side by Stacks 0BEU, right side by 02SQ + projection formula +
`deg ∘ ι_* = deg`, then the induction hypothesis `P(k, d)` for `D` (projective as a closed
subscheme of `X`). -/
theorem snapperEqChow_divisor_case (k : Type u) [Field k] (d : ℕ) (ih : SnapperEqChowInDim k d)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (hXproj : IsProjectiveOver k X) [IsLocallyNoetherian X] [IsIntegral X]
    (hd : X.dimension = d + 1) (L : Fin (d + 1) → X.Modules) [∀ i, (L i).IsLineBundle]
    (D : EffectiveCartierDivisor X) [∀ j, (Function.update L 0 D.lineBundle j).IsLineBundle] :
    snapperIntersection X hX hd (Function.update L 0 D.lineBundle)
      = chowSideFunctional X hX L (ratDivisorOpOfLineBundle D.lineBundle) := by
  have hprop : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have hft : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k)) := hprop.toLocallyOfFiniteType
  by_cases hD : D.idealSheaf = ⊤
  · -- `D = ∅`: `O(D) ≅ O_X`, both sides are `0`
    obtain ⟨e⟩ := D.nonempty_lineBundle_iso_unit_of_eq_top hD
    rw [snapperIntersection_eq_zero_of_iso_unit X hX hd (Function.update L 0 D.lineBundle) 0
      (eqToIso (Function.update_self 0 D.lineBundle L) ≪≫ e),
      ratDivisorOpOfLineBundle_congr _ _ e, ratDivisorOpOfLineBundle_unit, chowSideFunctional_zero]
  · -- `D ≠ ∅`
    have hdD : D.toScheme.dimension = d := D.toScheme_dimension_eq hX hd hD
    -- `letI` (inlined) so that the instance agrees syntactically with the one in 0BEU's statement
    letI : D.toScheme.Over (Spec (CommRingCat.of k)) :=
      ⟨D.idealSheaf.subschemeι ≫ (X ↘ Spec (CommRingCat.of k))⟩
    have hιo : D.idealSheaf.subschemeι.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
    have hD' : IsProperOver k D.toScheme := isProperOver_of_closedImmersion hX D.idealSheaf.subschemeι
    have hDproj : IsProjectiveOver k D.toScheme :=
      IsProjectiveOver.of_isClosedImmersion D.idealSheaf.subschemeι hXproj
    have hpropD : IsProper (D.toScheme ↘ Spec (CommRingCat.of k)) := hD'
    have hftD : LocallyOfFiniteType (D.toScheme ↘ Spec (CommRingCat.of k)) :=
      hpropD.toLocallyOfFiniteType
    -- Step 4: left side by Stacks 0BEU
    have hL : Nonempty (Function.update L 0 D.lineBundle 0 ≅ D.lineBundle) :=
      ⟨eqToIso (Function.update_self 0 D.lineBundle L)⟩
    have h0beu := snapperIntersection_effectiveCartier X hX hd (Function.update L 0 D.lineBundle) D hL hdD
    have hfam : (fun i : Fin d => (Scheme.Modules.pullback D.idealSheaf.subschemeι).obj
        (Function.update L 0 D.lineBundle i.succ))
        = fun i => (Scheme.Modules.pullback D.idealSheaf.subschemeι).obj (L i.succ) := by
      funext i
      rw [Function.update_of_ne (Fin.succ_ne_zero i)]
    rw [snapperIntersection_congr_fun _ _ _ _ _ hfam] at h0beu
    -- Step 6: the induction hypothesis for `D`
    have hih := ih D.toScheme hD' hDproj hdD
      (fun i => (Scheme.Modules.pullback D.idealSheaf.subschemeι).obj (L i.succ))
    unfold SnapperEqChowFor at hih
    rw [h0beu, hih]
    -- Step 5: right side
    rw [chowSideFunctional_def]
    have hcap : ratDivisorOpOfLineBundle D.lineBundle d ((1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass (d + 1))
        = chowPushforwardRat D.idealSheaf.subschemeι d
          ((1 : ℚ) ⊗ₜ[ℤ] D.toScheme.fundamentalChowClass d) := by
      show (firstChernClass D.lineBundle (d + 1)).ratExtend _
        = (chowPushforward D.idealSheaf.subschemeι d).ratExtend _
      rw [AddMonoidHom.ratExtend_tmul, AddMonoidHom.ratExtend_tmul,
        D.firstChernClass_cap_fundamentalChowClass (k := k) d hd]
    rw [hcap]
    obtain ⟨w, hw⟩ : ∃ w : ChowGroupRat D.toScheme d,
        (1 : ℚ) ⊗ₜ[ℤ] D.toScheme.fundamentalChowClass d = w := ⟨_, rfl⟩
    rw [hw]
    rw [ChowGroupRat.eqRec_eq_congr, ← chowPushforwardRat_congr_index,
      RatDivisorOp.capProd_chowPushforwardRat (k := k) D.idealSheaf.subschemeι
        (fun i : Fin d => L i.succ) 0,
      ChowGroupRat.degree_chowPushforwardRat hD' hX D.idealSheaf.subschemeι]

/-- **Stacks 0BFI, inductive step for projective integral `X`** (see the module docstring). -/
theorem snapperEqChowFor_of_projective_succ (k : Type u) [Field k] (d : ℕ)
    (ih : AlgebraicGeometry.SnapperEqChowInDim k d)
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) (_ : IsProjectiveOver k X)
    [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X]
    (hd : X.dimension = d + 1) (L : Fin (d + 1) → X.Modules) [∀ i, (L i).IsLineBundle] :
    AlgebraicGeometry.SnapperEqChowFor X hX hd L := by
  obtain hXproj : IsProjectiveOver k X := by assumption
  have hprop : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have hft : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k)) := hprop.toLocallyOfFiniteType
  unfold SnapperEqChowFor
  rw [chowSide_eq_chowSideFunctional X hX L]
  -- Step 2: `L_0 ≅ O(A) ⊗ O(B)^∨` (Stacks 0AYM)
  obtain ⟨A, B, ⟨e⟩⟩ := exists_effectiveCartierDivisor_sub X hXproj (L 0)
  have hA := isLineBundle_update L 0 A.lineBundle
  have hBd := isLineBundle_update L 0 (Scheme.Modules.dual B.lineBundle)
  have hB := isLineBundle_update L 0 B.lineBundle
  have hU := isLineBundle_update L 0 (SheafOfModules.unit X.ringCatSheaf : X.Modules)
  -- Step 1, left side: additivity (0BER), `(O_X ⋯) = 0`, and `O_X ≅ O(B) ⊗ O(B)^∨`
  have h1 := snapperIntersection_tensor X hX hd L 0 A.lineBundle (Scheme.Modules.dual B.lineBundle) e
  obtain ⟨eB⟩ := SheafOfModules.IsLineBundle.tensor_dual_iso B.lineBundle
  have hBB := isLineBundle_update (Function.update L 0 (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    0 B.lineBundle
  have hBBd := isLineBundle_update (Function.update L 0 (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    0 (Scheme.Modules.dual B.lineBundle)
  have h2 := snapperIntersection_tensor X hX hd
    (Function.update L 0 (SheafOfModules.unit X.ringCatSheaf : X.Modules)) 0 B.lineBundle
    (Scheme.Modules.dual B.lineBundle)
    (eqToIso (Function.update_self 0 (SheafOfModules.unit X.ringCatSheaf : X.Modules) L) ≪≫ eB.symm)
  rw [snapperIntersection_congr_fun X hX hd _ _
      (Function.update_idem (α := Fin (d + 1)) (a := 0) (SheafOfModules.unit X.ringCatSheaf : X.Modules)
        B.lineBundle L),
    snapperIntersection_congr_fun X hX hd _ _
      (Function.update_idem (α := Fin (d + 1)) (a := 0) (SheafOfModules.unit X.ringCatSheaf : X.Modules)
        (Scheme.Modules.dual B.lineBundle) L)] at h2
  have h3 := snapperIntersection_update_unit X hX hd L 0
  -- Steps 3–6 for `A` and `B`
  have hAeq := snapperEqChow_divisor_case k d ih X hX hXproj hd L A
  have hBeq := snapperEqChow_divisor_case k d ih X hX hXproj hd L B
  -- Step 1, right side: additivity of `c_1`
  have : (Scheme.Modules.tensor A.lineBundle (Scheme.Modules.dual B.lineBundle)).IsLineBundle :=
    Scheme.Modules.IsLineBundle.of_iso e
  have : (Scheme.Modules.tensor B.lineBundle (Scheme.Modules.dual B.lineBundle)).IsLineBundle :=
    Scheme.Modules.IsLineBundle.of_iso eB.symm
  have c1 : ratDivisorOpOfLineBundle (L 0)
      = ratDivisorOpOfLineBundle A.lineBundle + ratDivisorOpOfLineBundle (Scheme.Modules.dual B.lineBundle) := by
    rw [ratDivisorOpOfLineBundle_congr _ _ e, ratDivisorOpOfLineBundle_tensor (k := k)]
  have c2 : (0 : RatDivisorOp X)
      = ratDivisorOpOfLineBundle B.lineBundle + ratDivisorOpOfLineBundle (Scheme.Modules.dual B.lineBundle) := by
    rw [← ratDivisorOpOfLineBundle_tensor (k := k), ratDivisorOpOfLineBundle_congr _ _ eB,
      ratDivisorOpOfLineBundle_unit]
  have c3 := congrArg (chowSideFunctional X hX L) c2
  rw [chowSideFunctional_add, chowSideFunctional_zero] at c3
  rw [c1, chowSideFunctional_add]
  linarith

end AlgebraicGeometry

end
