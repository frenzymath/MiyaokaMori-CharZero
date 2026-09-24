import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.FrameJetCoefficientMap
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.TotalSpaceFrameMonomial
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivizeSymCoeffAux

/-! # The ring map `Φ₁ = φ_J^♯ ∘ χ_V : J_κ(B_V, s^♯) → Γ(Tot(L), p⁻¹U)` and its values on generators
(steps 2–3 of the proof of Lemma 3.1 of the paper)

`φ_J := J.jetPoint : Tot(L) → J_κ^s` is the point of the affine jet scheme given by the based jet `J`;
its ring map on the functions over `V`, composed with the chart identification
`χ_V = chartEquiv V : J_κ(B_V, s^♯) ≃+* Γ(J_κ^s, π⁻¹V)` and restricted to `Tot|_U = p⁻¹U` (`U ≤ ρ⁻¹V`), is a
ring homomorphism `Φ₁ : J_κ(B_V, s^♯) →+* Γ(Tot(L), p⁻¹U)` (`jetPointRingHom`). On the constants it is
`p^♯ ∘ ρ^♯` (`jetPointRingHom_algebraMap`: `chartEquiv_unitHom`, `Over.w J.jetPoint`), and when
`J|_{p_L⁻¹U} = localJet (frameJetRingMap μ φ)`, on the jet coordinate `d_q c` it is
`p^♯(φ(d_q c)) · 𝔪^{q+1}` (`jetPointRingHom_coeffClass_of_localJet`: `jetPoint_appLE_jetCoordinate`
restricted to `U`, `pieceSection_of_localJet`, `frameJetRingMap_π`, and `𝒪`-linearity of `pieceIso ≫ frameHom`).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace jetNeighborhood

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
  (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ)

/-- `Tot(L) → C̃ → C` pulls `V` back inside `φ_J⁻¹(π⁻¹V)` (`Over.w J.jetPoint`). -/
theorem totOver_preimage_le_jetPoint_preimage (V : C.toScheme.Opens) :
    (BasedJet.totOver ρ L).hom ⁻¹ᵁ V ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V) := by
  rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, CategoryTheory.Over.w]

/-- `p⁻¹U ≤ (p ≫ ρ)⁻¹V` for `U ≤ ρ⁻¹V`. -/
theorem tot_preimage_le_totOver_preimage {V : C.toScheme.Opens} {U : ρ.source.toScheme.Opens}
    (hUV : U ≤ ρ.hom ⁻¹ᵁ V) :
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U ≤ (BasedJet.totOver ρ L).hom ⁻¹ᵁ V :=
  fun _ hx => hUV hx

/-- `p⁻¹U ≤ φ_J⁻¹(π⁻¹V)` for `U ≤ ρ⁻¹V`. -/
theorem tot_preimage_le_jetPoint_preimage {V : C.toScheme.Opens} {U : ρ.source.toScheme.Opens}
    (hUV : U ≤ ρ.hom ⁻¹ᵁ V) :
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V) :=
  fun _ hx => totOver_preimage_le_jetPoint_preimage f κ ρ L J V (tot_preimage_le_totOver_preimage ρ L hUV hx)

variable {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
  {U : ρ.source.toScheme.Opens} (hUV : U ≤ ρ.hom ⁻¹ᵁ V)

/-- **`Φ₁`**: the ring map `φ_J^♯ ∘ χ_V : J_κ(B_V, s^♯) →+* Γ(Tot(L), p⁻¹U)`. -/
def jetPointRingHom : coneJetAlgebra f κ V →+*
    Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U) :=
  (J.jetPoint.left.appLE
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V)
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U)
      (tot_preimage_le_jetPoint_preimage f κ ρ L J hUV)).hom.comp
    (relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
      ⟨V, hV⟩).toRingHom

theorem jetPointRingHom_apply (y : coneJetAlgebra f κ V) :
    jetPointRingHom f κ ρ L J hV hUV y =
      (J.jetPoint.left.appLE
        ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V)
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U)
        (tot_preimage_le_jetPoint_preimage f κ ρ L J hUV)).hom
      (relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hV⟩ y) :=
  rfl

/-- `Φ₁` on the constants: `Φ₁(algebraMap r) = p^♯(ρ^♯ r)` (`chartEquiv_unitHom`, `Over.w J.jetPoint`). -/
theorem jetPointRingHom_algebraMap (r : Γ(C.toScheme, V)) :
    letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
    jetPointRingHom f κ ρ L J hV hUV (algebraMap Γ(C.toScheme, V) (coneJetAlgebra f κ V) r) =
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app U).hom ((ρ.hom.appLE V U hUV).hom r) := by
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  set π := (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom with hπ
  set Tot := AlgebraicGeometry.Scheme.totalSpace L.toModules with hTot
  have h0 : relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hV⟩
      (algebraMap Γ(C.toScheme, V) (coneJetAlgebra f κ V) r) = (π.app V).hom r :=
    relativeJetScheme.chartEquiv_unitHom (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hV⟩ r
  have hle' : Tot.hom ⁻¹ᵁ U ≤ (J.jetPoint.left ≫ π) ⁻¹ᵁ V := tot_preimage_le_jetPoint_preimage f κ ρ L J hUV
  have hle'' : Tot.hom ⁻¹ᵁ U ≤ (Tot.hom ≫ ρ.hom) ⁻¹ᵁ V := fun _ hx => hUV hx
  have h1 : (J.jetPoint.left.appLE (π ⁻¹ᵁ V) (Tot.hom ⁻¹ᵁ U)
      (tot_preimage_le_jetPoint_preimage f κ ρ L J hUV)).hom ((π.app V).hom r) =
      ((J.jetPoint.left ≫ π).appLE V (Tot.hom ⁻¹ᵁ U) hle').hom r := rfl
  have h2 : (J.jetPoint.left ≫ π).appLE V (Tot.hom ⁻¹ᵁ U) hle' =
      (Tot.hom ≫ ρ.hom).appLE V (Tot.hom ⁻¹ᵁ U) hle'' :=
    AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (CategoryTheory.Over.w J.jetPoint) V _ hle' hle''
  have h3 : ((Tot.hom ≫ ρ.hom).appLE V (Tot.hom ⁻¹ᵁ U) hle'').hom r =
      (Tot.hom.appLE U (Tot.hom ⁻¹ᵁ U) le_rfl).hom ((ρ.hom.appLE V U hUV).hom r) :=
    (congrArg (fun g : Γ(C.toScheme, V) ⟶ Γ(Tot.left, Tot.hom ⁻¹ᵁ U) => g.hom r)
      (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE Tot.hom ρ.hom V U (Tot.hom ⁻¹ᵁ U) hUV le_rfl)).symm
  have h4 : (Tot.hom.appLE U (Tot.hom ⁻¹ᵁ U) le_rfl).hom ((ρ.hom.appLE V U hUV).hom r) =
      (Tot.hom.app U).hom ((ρ.hom.appLE V U hUV).hom r) :=
    congrArg (fun g : Γ(ρ.source.toScheme, U) ⟶ Γ(Tot.left, Tot.hom ⁻¹ᵁ U) => g.hom ((ρ.hom.appLE V U hUV).hom r))
      (AlgebraicGeometry.Scheme.Hom.app_eq_appLE Tot.hom).symm
  refine (jetPointRingHom_apply f κ ρ L J hV hUV _).trans ?_
  refine (congrArg (J.jetPoint.left.appLE (π ⁻¹ᵁ V) (Tot.hom ⁻¹ᵁ U)
    (tot_preimage_le_jetPoint_preimage f κ ρ L J hUV)).hom h0).trans ?_
  exact h1.trans ((congrArg (fun g : Γ(C.toScheme, V) ⟶ Γ(Tot.left, Tot.hom ⁻¹ᵁ U) => g.hom r) h2).trans
    (h3.trans h4))

variable (μ : Γ((L.zpow (-1)).toModules, U)) (hU : AlgebraicGeometry.IsAffineOpen U)
  (φ : letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
    letI := baseAlgebra ρ hUV
    coneJetAlgebra f κ V →ₐ[Γ(C.toScheme, V)] Γ(ρ.source.toScheme, U))

/-- `Φ₁` on the jet coordinates when `J|_{p_L⁻¹U} = localJet (frameJetRingMap μ φ)`:
`Φ₁(d_q c) = p^♯(φ(d_q c)) · 𝔪^{q+1}`. -/
theorem jetPointRingHom_coeffClass_of_localJet
    (hJ : (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι ≫ J.hom =
      localJet f κ ρ L hV hU (frameJetRingMap f κ ρ L hUV μ φ))
    (q : Fin κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)) :
    letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
    jetPointRingHom f κ ρ L J hV hUV
        (BasedJetAlgebra.coeffClass
          (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) κ
          ((q : ℕ) + 1) c) =
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app U).hom
        (φ (BasedJetAlgebra.coeffClass
          (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) κ
          ((q : ℕ) + 1) c)) * frameMonomial L U μ ((q : ℕ) + 1) := by
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  letI := baseAlgebra ρ hUV
  set π := (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom with hπ
  set Tot := AlgebraicGeometry.Scheme.totalSpace L.toModules with hTot
  have hUc := relativeJetScheme.preimage_eq_chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 κ ⟨V, hV⟩
  have hχ := relativeJetScheme.chartEquiv_eq_chartSections (k := k) (MMSetup.cone f)
    (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hV⟩ hUc
    (BasedJetAlgebra.coeffClass
      (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) κ ((q : ℕ) + 1) c)
  have hle := totOver_preimage_le_jetPoint_preimage f κ ρ L J V
  refine (jetPointRingHom_apply f κ ρ L J hV hUV _).trans ?_
  refine (congrArg (J.jetPoint.left.appLE (π ⁻¹ᵁ V) (Tot.hom ⁻¹ᵁ U)
    (tot_preimage_le_jetPoint_preimage f κ ρ L J hUV)).hom hχ).trans ?_
  -- (1) restrict `φ_J^♯` from `p⁻¹ρ⁻¹V` to `p⁻¹U`
  have hres : ∀ z : Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
      π ⁻¹ᵁ V),
      (J.jetPoint.left.appLE (π ⁻¹ᵁ V) (Tot.hom ⁻¹ᵁ U) (tot_preimage_le_jetPoint_preimage f κ ρ L J hUV)).hom z =
      (Tot.left.presheaf.map (CategoryTheory.homOfLE (tot_preimage_le_totOver_preimage ρ L hUV)).op).hom
        ((J.jetPoint.left.appLE (π ⁻¹ᵁ V) ((BasedJet.totOver ρ L).hom ⁻¹ᵁ V) hle).hom z) := fun z =>
    (congrArg (fun g : Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
        π ⁻¹ᵁ V) ⟶ Γ(Tot.left, Tot.hom ⁻¹ᵁ U) => g.hom z)
      (AlgebraicGeometry.Scheme.Hom.appLE_map J.jetPoint.left hle
        (CategoryTheory.homOfLE (tot_preimage_le_totOver_preimage ρ L hUV)).op)).symm
  refine (hres _).trans ?_
  refine (congrArg (Tot.left.presheaf.map (CategoryTheory.homOfLE (tot_preimage_le_totOver_preimage ρ L hUV)).op).hom
    (J.jetPoint_appLE_jetCoordinate ⟨V, hV⟩ q c hUc hle)).trans ?_
  -- (2) naturality of `frameHom` under the restriction `U ≤ ρ⁻¹V`
  have hnat := PresheafOfModules.naturality_apply (BasedJet.frameHom L ((q : ℕ) + 1)).val
    (CategoryTheory.homOfLE hUV).op (J.pieceSection V ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2) c)
  refine Eq.trans ?_ (hnat.symm.trans ?_)
  · rfl
  -- (3) the restricted piece section is `pieceIso (π_{q+1}(Ψ c)) = pieceIso (φ(d_q c) • μ^{⊗(q+1)})`
  rw [pieceSection_of_localJet f κ ρ L hV hU hUV J _ hJ ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2) c,
    frameJetRingMap_π f κ ρ L hUV μ φ ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2) c]
  -- (4) `𝒪(U)`-linearity of `pieceIso ≫ frameHom`
  set a := φ (BasedJetAlgebra.coeffClass
    (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) κ ((q : ℕ) + 1) c)
    with ha
  set t := truncatedJetAlgebra.framePow L U μ ((q : ℕ) + 1) with ht
  refine (congrArg ((BasedJet.frameHom L ((q : ℕ) + 1)).val.app (Opposite.op U)).hom
    (LinearMap.map_smul ((truncatedJetAlgebra.pieceIso L ((q : ℕ) + 1)).hom.val.app (Opposite.op U)).hom a t)).trans ?_
  refine (LinearMap.map_smul ((BasedJet.frameHom L ((q : ℕ) + 1)).val.app (Opposite.op U)).hom a _).trans ?_
  exact pushforward_unit_smul_eq L U a _

end jetNeighborhood

end
