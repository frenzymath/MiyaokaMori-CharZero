import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGradedAlgebraSectionsBridge
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetRescalingAction
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraLocallyWeightedPolynomial
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaQuasicoherent
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraGrading
import MiyaokaMori.RingTheory.GradedRing.ReesAlgebra

/-! # The linear piece of the jet algebra: definitions and the chart reading of `Γ(U, S_m)`

Shared base of the coefficient maps and of the bijectivity of the coefficient morphism
(`DeformedJetAlgebraFiberAtZero_LinearPieceDual`).

Notation: `Ω' := sec^*Ω_{Z/C}`, `S := (jetGradedAlgebra Z sec hs r).1` (the weight decomposition of `π_*O_J` under the
rescaling action, `S_m = ker φ_m`), `L_{q+1} := S_{q+1}/I^{(2)}_{q+1} = cokernel (S.irrelevantPow 2 (q+1)).2`; for an
affine `U ⊆ C`: `A := Γ(C, U)`, `B := Γ(Z, π⁻¹U)`, `ε := sec^♯ : B → A` (`relativeJetScheme.augmentation`),
`J := J_r(B, ε) = BasedJetAlgebra ε r` (the chart ring, `relativeJetScheme.chartEquiv : J ≃+* Γ(π⁻¹U, O_J)`),
`d_q b := coeffClass ε r (q+1) b ∈ J`.

Contents:
* `jetLinearPiece.omegaSection U b := (db)|_sec ∈ Γ(U, Ω')`, `jetLinearPiece.jetSection U m : Γ(U, S_m) → J`
  (`kernel.ι` on sections followed by `chartEquiv⁻¹`), `jetLinearPiece.IsCoefficientHom` (the characterisation of the
  coefficient morphism `θ_q : Ω' ⟶ L_{q+1}`, `(db)|_sec ↦ [d_q b]`).
* `jetSection` is additive, `A`-linear (`jetSection_smul`: `js (a • x) = algebraMap a * js x`; `kernel.ι` is
  `O_C`-linear, the `A`-action on `Γ(π⁻¹U, O_J) = Γ(U, π_*O_J)` is `a • y = π^♯(a) · y`, and
  `χ⁻¹(π^♯ a) = algebraMap a` by `chartEquiv_unitHom`), injective (`weightPartιApp_injective`), lands in
  `grading ε r m` and hits all of it (`weightDefect_app_chartEquiv_eq_zero_iff` + `exists_kernel_section`,
  `kernel_ι_app_apply`); packaged as `jetSectionLin : Γ(U, S_m) →ₗ[A] J`.
* `jetLinearPiece.toSectionsRing : J →+* S.sectionsRing U` — the inverse `Ψ⁻¹` of the graded ring isomorphism
  `Ψ := χ⁻¹ ∘ ψ_U : S.sectionsRing U → J` (`ψ_U = gradedAlgebra_sectionsToRingHom`, bijective by
  `gradedAlgebra_sectionsToRingHom_injective` / `_surjective` + `jetRescalingAction_isNonnegative`), with
  `toSectionsRing (jetSection x) = S.ofPiece U m x` and graded (`toSectionsRing_mem_gradingSubmodule`).
* Consequence (`exists_irrelevantPow_app_eq_of_jetSection_mem_irrPow`): if `js x ∈ (J_+)^p ∩ J_j`
  (`ReesAlgebra.irrPow (grading ε r) p j`) then `x` is in the image of `Γ(U, I^{(p)}_j) → Γ(U, S_j)`
  (`ReesAlgebra.map_mem_irrPow` for `Ψ⁻¹` + `irrelevantPow_app_range_iff`). In particular such `x` die in `Γ(U, L_j)`.

Source: §2 of the paper (`𝒮 = ⊕ 𝒮_m`; eq. (2.7)); Stacks 0EKK (`𝔾_m`-action ⟺ grading). Edge cases:
`U = ⊥` (zero rings), `r = 0` (`J = A`, only weight 0), `m > r` (`Γ(U, S_m) = 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

section CoefficientHom

variable {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (r : ℕ)

/-- `(db)|_sec ∈ Γ(U, sec^*Ω_{Z/C})` for `b ∈ Γ(π⁻¹U, O_Z)`: the universal derivation `d_{Z/C}` on `π⁻¹U`
(`Omega.universalDerivation`) followed by the section pullback `Γ(π⁻¹U, Ω_{Z/C}) → Γ(sec⁻¹π⁻¹U, sec^*Ω_{Z/C})`
restricted to `U ≤ sec⁻¹π⁻¹U` (in fact `sec⁻¹π⁻¹U = U`, `relativeJetScheme.section_preimage_le`). Over an affine `U`
these sections generate `Γ(U, sec^*Ω_{Z/C}) ≅ Γ(C,U) ⊗_{Γ(Z,π⁻¹U)} Ω_{Γ(Z,π⁻¹U)/Γ(C,U)}` (Stacks 01I9 + 01UT). -/
def jetLinearPiece.omegaSection (U : C.toScheme.Opens) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U)) :
    Γ((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom), U) :=
  AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn sec (AlgebraicGeometry.Omega Z.hom) (Z.hom ⁻¹ᵁ U) U
    (relativeJetScheme.section_preimage_le Z sec hs U)
    ((AlgebraicGeometry.Omega.universalDerivation Z.hom).d (X := Opposite.op (Z.hom ⁻¹ᵁ U)) b)

/-- A section of the weight-`m` piece `S_m = ker(weight defect φ_m)` of the jet graded algebra over an affine `U`,
read in the chart ring `J_r(B_U, ε_U)`: `Γ(U, S_m) → Γ(π⁻¹U, O_J)` (`kernel.ι`, `weightPartιApp`) followed by
`chartEquiv⁻¹ : Γ(π⁻¹U, O_J) ≃+* J_r(B_U, ε_U)`. It is additive and injective (`weightPartιApp_injective`), and its image
is `BasedJetAlgebra.grading ε_U r m` (`relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff` +
`exists_kernel_section`, as in `jetGradedAlgebra_sections_equiv_jetGradedAffineAlgebra`). -/
def jetLinearPiece.jetSection (U : C.toScheme.affineOpens) (m : ℕ)
    (x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1)) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    BasedJetAlgebra (relativeJetScheme.augmentation Z sec hs U.1) r :=
  (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).symm
    (GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) m U.1 x)

/-- **The characterisation of the coefficient morphism** `θ_q : sec^*Ω_{Z/C} ⟶ L_{q+1} := S_{q+1}/I^{(2)}_{q+1}`:
over every affine `U`, `θ_q` sends `(db)|_sec` to the class `[d_q b]` of the `(q+1)`-st jet coefficient of
`b ∈ Γ(π⁻¹U, O_Z)` — phrased as: whenever `x ∈ Γ(U, S_{q+1})` reads as `d_q b = coeffClass ε_U r (q+1) b` in the chart
ring, `θ_q.app U ((db)|_sec) = cokernel.π.app U x`. Since the `(db)|_sec` generate `Γ(U, sec^*Ω)` and `θ_q.app U` is
`Γ(C,U)`-linear, this determines `θ_q.app U` on every affine `U`, hence `θ_q`. -/
def jetLinearPiece.IsCoefficientHom (q : Fin r)
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom) ⟶
      CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2) :
    Prop :=
  ∀ (U : C.toScheme.affineOpens) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1))
    (x : ((jetGradedAlgebra (k := k) Z sec hs r).1.part (q.1 + 1)).val.obj (Opposite.op U.1)),
    (letI := relativeJetScheme.sectionsAlgebra Z U.1;
      jetLinearPiece.jetSection Z sec hs r U (q.1 + 1) x =
        BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z sec hs U.1) r (q.1 + 1) b) →
    (θ.app U.1).hom (jetLinearPiece.omegaSection Z sec hs U.1 b) =
      ((CategoryTheory.Limits.cokernel.π
        ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).app U.1).hom x

namespace jetLinearPiece

variable (U : C.toScheme.affineOpens) (m : ℕ)

theorem jetSection_add (x y : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1)) :
    jetSection Z sec hs r U m (x + y) = jetSection Z sec hs r U m x + jetSection Z sec hs r U m y :=
  (congrArg (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).symm
    (map_add (GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) m U.1) x y)).trans
    (map_add _ _ _)

theorem jetSection_zero :
    jetSection Z sec hs r U m (0 : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1)) = 0 :=
  (congrArg (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).symm
    (map_zero (GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) m U.1))).trans
    (map_zero _)

/-- `Γ(C,U)`-linearity of the chart reading: `js (a • x) = algebraMap a * js x`. -/
theorem jetSection_smul (a : Γ(C.toScheme, U.1))
    (x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1)) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    jetSection Z sec hs r U m (a • x) =
      algebraMap Γ(C.toScheme, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z sec hs U.1) r) a *
        jetSection Z sec hs r U m x := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have h1 : GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) m U.1 (a • x) =
      ((relativeJetScheme (k := k) Z sec hs r).hom.app U.1).hom a *
        GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) m U.1 x :=
    AlgebraicGeometry.Scheme.Modules.Hom.app_smul
      (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z sec hs r) m))
      a x
  have h2 : (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).symm
      (((relativeJetScheme (k := k) Z sec hs r).hom.app U.1).hom a) =
      algebraMap Γ(C.toScheme, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z sec hs U.1) r) a :=
    (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).injective
      ((RingEquiv.apply_symm_apply _ _).trans
        (relativeJetScheme.chartEquiv_unitHom (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U) a).symm)
  show (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).symm
    (GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) m U.1 (a • x)) = _
  exact (congrArg (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).symm
    h1).trans ((map_mul _ _ _).trans (congrArg (· * _) h2))

theorem jetSection_injective : Function.Injective (jetSection Z sec hs r U m) := fun _ _ hxy =>
  GroupSchemeAction.weightPartιApp_injective (jetRescalingAction (k := k) Z sec hs r) m U.1
    ((relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).symm.injective hxy)

/-- The chart reading of a weight-`m` section lies in the `m`-th grading piece of the chart ring. -/
theorem jetSection_mem_grading (x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1)) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    jetSection Z sec hs r U m x ∈ BasedJetAlgebra.grading (relativeJetScheme.augmentation Z sec hs U.1) r m := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have h := (relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff (k := k) Z sec hs r
    (AlgebraicGeometry.Scheme.affineSite U) m (jetSection Z sec hs r U m x)).mp
  refine h ?_
  have e : (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U))
      (jetSection Z sec hs r U m x) =
      GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) m U.1 x :=
    RingEquiv.apply_symm_apply _ _
  refine Eq.trans (congrArg _ e) ?_
  exact AlgebraicGeometry.Scheme.Modules.kernel_ι_app_apply
    (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z sec hs r) m) U.1 x

/-- Every element of the `m`-th grading piece of the chart ring is the chart reading of a weight-`m` section. -/
theorem exists_jetSection_eq
    (z : letI := relativeJetScheme.sectionsAlgebra Z U.1
      BasedJetAlgebra (relativeJetScheme.augmentation Z sec hs U.1) r)
    (hz : letI := relativeJetScheme.sectionsAlgebra Z U.1
      z ∈ BasedJetAlgebra.grading (relativeJetScheme.augmentation Z sec hs U.1) r m) :
    ∃ x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1), jetSection Z sec hs r U m x = z := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have h0 := (relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff (k := k) Z sec hs r
    (AlgebraicGeometry.Scheme.affineSite U) m z).mpr hz
  obtain ⟨x, hx⟩ := AlgebraicGeometry.Scheme.Modules.exists_kernel_section
    (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z sec hs r) m) U.1 _ h0
  refine ⟨x, ?_⟩
  show (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).symm
    (GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) m U.1 x) = z
  refine (congrArg (relativeJetScheme.chartEquiv (k := k) Z sec hs r
    (AlgebraicGeometry.Scheme.affineSite U)).symm hx).trans ?_
  exact RingEquiv.symm_apply_apply _ _

/-- The chart reading as a `Γ(C,U)`-linear map `Γ(U, S_m) →ₗ J_r(B_U, ε_U)`. -/
def jetSectionLin :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1) →ₗ[Γ(C.toScheme, U.1)]
      BasedJetAlgebra (relativeJetScheme.augmentation Z sec hs U.1) r :=
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  { toFun := jetSection Z sec hs r U m
    map_add' := jetSection_add Z sec hs r U m
    map_smul' := fun a x =>
      (jetSection_smul Z sec hs r U m a x).trans (Algebra.smul_def a _).symm }

theorem jetSectionLin_apply (x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1)) :
    jetSectionLin Z sec hs r U m x = jetSection Z sec hs r U m x := rfl

/-! ## The inverse `Ψ⁻¹ : J_r(B_U, ε_U) → S(U)` of the graded ring isomorphism `χ⁻¹ ∘ ψ_U` -/

/-- The sections ring homomorphism `ψ_U : S(U) = ⊕_m Γ(U, S_m) → Γ(π⁻¹U, O_J)`, with target written as `Γ(π⁻¹U, O_J)`
(the ring structure of `(π_*O_J).sectionsRing U` is that of `Γ(π⁻¹U, O_J)`: `pushforwardStructureSheaf.sectionsRing_mul`,
`_one`). -/
def sectionsToGamma :
    ((jetGradedAlgebra (k := k) Z sec hs r).1).sectionsRing U.1 →+*
      Γ((relativeJetScheme (k := k) Z sec hs r).left, (relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ U.1) where
  toFun x := show Γ((relativeJetScheme (k := k) Z sec hs r).left, (relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ U.1)
    from GroupSchemeAction.gradedAlgebra_sectionsToRingHom (jetRescalingAction (k := k) Z sec hs r) U.1 x
  map_one' := (congrArg (fun y : (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf
      (relativeJetScheme (k := k) Z sec hs r).hom).sectionsRing U.1 =>
      show Γ((relativeJetScheme (k := k) Z sec hs r).left, (relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ U.1) from y)
    (map_one (GroupSchemeAction.gradedAlgebra_sectionsToRingHom (jetRescalingAction (k := k) Z sec hs r) U.1))).trans
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sectionsRing_one
      (relativeJetScheme (k := k) Z sec hs r).hom U.1)
  map_mul' x y := (congrArg (fun y : (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf
      (relativeJetScheme (k := k) Z sec hs r).hom).sectionsRing U.1 =>
      show Γ((relativeJetScheme (k := k) Z sec hs r).left, (relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ U.1) from y)
    (map_mul (GroupSchemeAction.gradedAlgebra_sectionsToRingHom (jetRescalingAction (k := k) Z sec hs r) U.1) x y)).trans
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sectionsRing_mul
      (relativeJetScheme (k := k) Z sec hs r).hom U.1 _ _)
  map_zero' := congrArg (fun y : (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf
      (relativeJetScheme (k := k) Z sec hs r).hom).sectionsRing U.1 =>
      show Γ((relativeJetScheme (k := k) Z sec hs r).left, (relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ U.1) from y)
    (map_zero (GroupSchemeAction.gradedAlgebra_sectionsToRingHom (jetRescalingAction (k := k) Z sec hs r) U.1))
  map_add' x y := congrArg (fun y : (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf
      (relativeJetScheme (k := k) Z sec hs r).hom).sectionsRing U.1 =>
      show Γ((relativeJetScheme (k := k) Z sec hs r).left, (relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ U.1) from y)
    (map_add (GroupSchemeAction.gradedAlgebra_sectionsToRingHom (jetRescalingAction (k := k) Z sec hs r) U.1) x y)

theorem sectionsToGamma_ofPiece (x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1)) :
    sectionsToGamma Z sec hs r U (((jetGradedAlgebra (k := k) Z sec hs r).1).ofPiece U.1 m x) =
      GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) m U.1 x := by
  show GroupSchemeAction.gradedAlgebra_sectionsToRingHom (jetRescalingAction (k := k) Z sec hs r) U.1
    (((jetGradedAlgebra (k := k) Z sec hs r).1).ofPiece U.1 m x) = _
  exact (GroupSchemeAction.gradedAlgebra (jetRescalingAction (k := k) Z sec hs r)).sectionsToRingHom_of _ _
    (GroupSchemeAction.gradedAlgebra_one_comp_kernelι _) (GroupSchemeAction.gradedAlgebra_mul_comp_kernelι _) U.1 m x

theorem sectionsToGamma_bijective : Function.Bijective (sectionsToGamma Z sec hs r U) :=
  ⟨fun _ _ hxy => GroupSchemeAction.gradedAlgebra_sectionsToRingHom_injective
      (jetRescalingAction (k := k) Z sec hs r) U hxy,
    fun y => GroupSchemeAction.gradedAlgebra_sectionsToRingHom_surjective
      (jetRescalingAction (k := k) Z sec hs r) (jetRescalingAction_isNonnegative (k := k) Z sec hs r) U y⟩

/-- `Ψ⁻¹ : J_r(B_U, ε_U) →+* S(U)`: the chart identification `χ` followed by the inverse of `ψ_U`. -/
def toSectionsRing :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    BasedJetAlgebra (relativeJetScheme.augmentation Z sec hs U.1) r →+*
      ((jetGradedAlgebra (k := k) Z sec hs r).1).sectionsRing U.1 :=
  (RingEquiv.ofBijective (sectionsToGamma Z sec hs r U) (sectionsToGamma_bijective Z sec hs r U)).symm.toRingHom.comp
    (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).toRingHom

/-- `Ψ⁻¹ (js x) = of_m x`. -/
theorem toSectionsRing_jetSection (x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1)) :
    toSectionsRing Z sec hs r U (jetSection Z sec hs r U m x) =
      ((jetGradedAlgebra (k := k) Z sec hs r).1).ofPiece U.1 m x := by
  show (RingEquiv.ofBijective (sectionsToGamma Z sec hs r U) (sectionsToGamma_bijective Z sec hs r U)).symm
    ((relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U))
      ((relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)).symm
        (GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) m U.1 x))) = _
  refine (congrArg (RingEquiv.ofBijective (sectionsToGamma Z sec hs r U) (sectionsToGamma_bijective Z sec hs r U)).symm
    (RingEquiv.apply_symm_apply _ _)).trans ?_
  exact (RingEquiv.symm_apply_eq _).mpr (sectionsToGamma_ofPiece Z sec hs r U m x).symm

/-- `Ψ⁻¹` is graded: the `m`-th piece of the chart ring goes to the `m`-th piece of `S(U)`. -/
theorem toSectionsRing_mem_gradingSubmodule
    (z : letI := relativeJetScheme.sectionsAlgebra Z U.1
      BasedJetAlgebra (relativeJetScheme.augmentation Z sec hs U.1) r)
    (hz : letI := relativeJetScheme.sectionsAlgebra Z U.1
      z ∈ BasedJetAlgebra.grading (relativeJetScheme.augmentation Z sec hs U.1) r m) :
    (toSectionsRing Z sec hs r U z :
        ((jetGradedAlgebra (k := k) Z sec hs r).1).toGradedAffineAlgebra.toAffineAlgebra.sections
          (AlgebraicGeometry.Scheme.affineSite U)) ∈
      ((jetGradedAlgebra (k := k) Z sec hs r).1).toGradedAffineAlgebra.gradingSubmodule
        (AlgebraicGeometry.Scheme.affineSite U) m := by
  obtain ⟨x, rfl⟩ := exists_jetSection_eq Z sec hs r U m z hz
  rw [toSectionsRing_jetSection]
  exact ⟨x, rfl⟩

/-- **Elements of `(J_+)^p ∩ J_j` come from `I^{(p)}_j`**: if the chart reading of `x ∈ Γ(U, S_j)` lies in
`ReesAlgebra.irrPow (grading ε r) p j`, then `x` is in the image of `Γ(U, I^{(p)}_j) → Γ(U, S_j)`. -/
theorem exists_irrelevantPow_app_eq_of_jetSection_mem_irrPow (p j : ℕ)
    (x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part j, U.1))
    (hx : letI := relativeJetScheme.sectionsAlgebra Z U.1
      jetSection Z sec hs r U j x ∈
        ReesAlgebra.irrPow (BasedJetAlgebra.grading (relativeJetScheme.augmentation Z sec hs U.1) r) p j) :
    ∃ y, (((jetGradedAlgebra (k := k) Z sec hs r).1).irrelevantPow p j).2.app U.1 y = x := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have h := ReesAlgebra.map_mem_irrPow
    (BasedJetAlgebra.grading (relativeJetScheme.augmentation Z sec hs U.1) r)
    (((jetGradedAlgebra (k := k) Z sec hs r).1).toGradedAffineAlgebra.gradingSubmodule
      (AlgebraicGeometry.Scheme.affineSite U))
    (toSectionsRing Z sec hs r U) (fun m a ha => toSectionsRing_mem_gradingSubmodule Z sec hs r U m a ha) hx
  have h' := Eq.subst (motive := fun z => z ∈ ReesAlgebra.irrPow
      (((jetGradedAlgebra (k := k) Z sec hs r).1).toGradedAffineAlgebra.gradingSubmodule
        (AlgebraicGeometry.Scheme.affineSite U)) p j)
    (toSectionsRing_jetSection Z sec hs r U j x) h
  exact ((jetGradedAlgebra (k := k) Z sec hs r).1).irrelevantPow_app_range_iff
    (AlgebraicGeometry.Scheme.affineSite U) p j x |>.mpr h'

end jetLinearPiece

end CoefficientHom

end
