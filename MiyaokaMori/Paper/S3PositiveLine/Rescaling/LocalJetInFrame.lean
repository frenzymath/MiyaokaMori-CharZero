import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetOfRingMap
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Basis
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficient

/-! # The local jet in a frame: `Ψ = quotToSections_μ ∘ homEquiv φ`, and reading the pieces of `J`
(steps 1 and 4 of the proof of Lemma 3.1 of the paper)

In a frame `μ` of `L^{-1}` on the affine open `U`, `𝒜(U) ≅ 𝒪(U)[t]/(t^{κ+1})`, `t ↦ ι₁(μ)`
(`truncatedJetAlgebra.quotToSections`), and a `Γ(V)`-algebra map `φ : J_κ(B_V, s^♯) → 𝒪(U)` from the based
jet algebra of the cone over `V` corresponds to a based affine jet `B_V → 𝒪(U)[t]/(t^{κ+1})`
(`BasedJetAlgebra.homEquiv`): the paper's `(y, t) ↦ (ρ(y), Σ_q a_q(y) t^q)`. The composite
`Ψ := quotToSections_μ ∘ homEquiv φ : B_V → 𝒜(U)` (`frameJetRingMap`) is the ring map whose local jet
(`jetNeighborhood.localJet`) is the paper's local morphism. Its `n`-th piece is
`φ(d_{n-1} c) · μ^{⊗n}` (`frameJetRingMap_π`), it is compatible with the structure maps
(`frameJetRingMap_over`) and has constant term `s^♯` (`frameJetRingMap_π_zero`).

`pieceSection_of_localJet` reads the pieces of a based jet `J` on `U` from `J|_{p_L⁻¹U} = localJet Ψ`:
`J.pieceSection V n c |_U = pieceIso (π_n (Ψ c))`; combined with `BasedJet.weightComponent_jetCoordinate`
this identifies `Ψ_n(d_{n-1} c)|_U` for the jet coordinates `d_{n-1} c` (step 4 of the lemma).

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
  (L : LineBundle ρ.source.toVariety)

/-- The `Γ(C, V)`-algebra structure on `𝒪(U)` for `U ≤ ρ⁻¹V`, through `ρ^♯ : Γ(C, V) → 𝒪(U)`. -/
@[reducible] def baseAlgebra {V : C.toScheme.Opens} {U : ρ.source.toScheme.Opens} (hUV : U ≤ ρ.hom ⁻¹ᵁ V) :
    Algebra Γ(C.toScheme, V) Γ(ρ.source.toScheme, U) :=
  (ρ.hom.appLE V U hUV).hom.toAlgebra

/-- The based jet algebra `J_κ(B_V, s^♯)` of the cone over `V` (`relativeJetScheme.chartRing`
unbundled; the notation used throughout this construction). -/
abbrev coneJetAlgebra (V : C.toScheme.Opens) : Type u :=
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  BasedJetAlgebra (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) κ

variable {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
  {U : ρ.source.toScheme.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) (hUV : U ≤ ρ.hom ⁻¹ᵁ V)
  (μ : Γ((L.zpow (-1)).toModules, U))

/-- **The local jet ring map in a frame**: `Ψ = quotToSections_μ ∘ (homEquiv φ) : B_V → 𝒜(U)` for a
`Γ(V)`-algebra map `φ : J_κ(B_V, s^♯) → 𝒪(U)` (the coefficients) and a frame `μ` of `L^{-1}` on `U`
(the fibre coordinate `t = μ`). -/
def frameJetRingMap
    (φ : letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
      letI := baseAlgebra ρ hUV
      coneJetAlgebra f κ V →ₐ[Γ(C.toScheme, V)] Γ(ρ.source.toScheme, U)) :
    Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U) :=
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  letI := baseAlgebra ρ hUV
  CommRingCat.ofHom ((truncatedJetAlgebra.quotToSections L U μ κ).comp
    (BasedJetAlgebra.homEquiv
      (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) κ φ).1.toRingHom)

variable (φ : letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  letI := baseAlgebra ρ hUV
  coneJetAlgebra f κ V →ₐ[Γ(C.toScheme, V)] Γ(ρ.source.toScheme, U))

/-- **The pieces of `Ψ`**: `π_n (Ψ c) = φ(d_{n-1} c) • μ^{⊗n}` for `n ≤ κ`, where `d_{n-1} c =
coeffClass n c` (`homEquiv` reads coefficients: `universalJet_poly_coeff`, `mapTruncated_projection`;
`quotToSections_mk`, `π_polyToSections`). -/
theorem frameJetRingMap_π (n : ℕ) (hn : n ≤ κ)
    (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)) :
    letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨n, Nat.lt_succ_of_le hn⟩).app U ((frameJetRingMap f κ ρ L hUV μ φ).hom c) =
      φ (BasedJetAlgebra.coeffClass
          (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) κ n c) •
        truncatedJetAlgebra.framePow L U μ n := by
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  letI := baseAlgebra ρ hUV
  show (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨n, Nat.lt_succ_of_le hn⟩).app U (truncatedJetAlgebra.quotToSections L U μ κ
        (Ideal.Quotient.mk _ (Polynomial.map φ.toRingHom (∑ m ∈ Finset.range (κ + 1),
          Polynomial.monomial m (BasedJetAlgebra.coeffClass
            (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) κ m c))))) = _
  rw [truncatedJetAlgebra.quotToSections_mk, truncatedJetAlgebra.π_polyToSections]
  show Polynomial.coeff _ n • _ = _
  rw [Polynomial.coeff_map, BasedJetAlgebra.universalJet_poly_coeff _ κ c n hn]
  rfl

/-- **`Ψ` over the structure maps**: `Ψ(π^♯ r) = ρ^♯ r · 1` (`AlgHom.commutes`,
`quotToSections_comp_mk_comp_C`). -/
theorem frameJetRingMap_over (r : Γ(C.toScheme, V)) :
    (frameJetRingMap f κ ρ L hUV μ φ).hom
        (((MMSetup.cone f).hom.appLE V ((MMSetup.cone f).hom ⁻¹ᵁ V) le_rfl).hom r) =
      (truncatedJetAlgebra L κ).sectionsUnit U ((ρ.hom.appLE V U hUV).hom r) := by
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  letI := baseAlgebra ρ hUV
  have h1 : ((MMSetup.cone f).hom.appLE V ((MMSetup.cone f).hom ⁻¹ᵁ V) le_rfl).hom r =
      algebraMap Γ(C.toScheme, V) Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) r := by
    show _ = ((MMSetup.cone f).hom.app V).hom r
    rw [AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
  show truncatedJetAlgebra.quotToSections L U μ κ
    ((BasedJetAlgebra.homEquiv _ κ φ).1 (((MMSetup.cone f).hom.appLE V ((MMSetup.cone f).hom ⁻¹ᵁ V) le_rfl).hom r)) = _
  rw [h1, AlgHom.commutes]
  exact congrArg (fun ψ : Γ(ρ.source.toScheme, U) →+* (truncatedJetAlgebra L κ).sectionsRing U =>
      ψ ((ρ.hom.appLE V U hUV).hom r))
    (truncatedJetAlgebra.quotToSections_comp_mk_comp_C L U μ κ)

/-- **The constant term of `Ψ`**: `π₀ (Ψ c) = ρ^♯ (s^♯ c)` (`frameJetRingMap_π` at `n = 0`,
`coeffClass_zero_order`, `framePow_zero`; the augmentation of the cone is `s^♯`). -/
theorem frameJetRingMap_π_zero (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)) :
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩).app U ((frameJetRingMap f κ ρ L hUV μ φ).hom c) =
      (ρ.hom.appLE V U hUV).hom
        (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
          (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c) := by
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  letI := baseAlgebra ρ hUV
  rw [frameJetRingMap_π f κ ρ L hUV μ φ 0 (Nat.zero_le κ) c, BasedJetAlgebra.coeffClass_zero_order]
  have h1 : φ (Ideal.Quotient.mk _ (MvPolynomial.C
      ((relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) c))) =
      (ρ.hom.appLE V U hUV).hom
        (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
          (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c) :=
    φ.commutes _
  rw [h1, truncatedJetAlgebra.framePow_zero]
  show ((ρ.hom.appLE V U hUV).hom _ : Γ(ρ.source.toScheme, U)) • (1 : Γ(ρ.source.toScheme, U)) = _
  exact mul_one _

set_option backward.isDefEq.respectTransparency false in
/-- `topIso.hom ∘ D.ι.appLE D ⊤ = id` on `Γ(Y, D)` (both are `Y.presheaf.map` of an endomorphism of `D`
in `Y.Opens`, which is the identity). -/
theorem topIso_hom_ι_appLE_apply {Y : AlgebraicGeometry.Scheme.{u}} (D : Y.Opens)
    (e : (⊤ : D.toScheme.Opens) ≤ D.ι ⁻¹ᵁ D) (y : Γ(Y, D)) :
    D.topIso.hom.hom ((D.ι.appLE D ⊤ e).hom y) = y := by
  rw [AlgebraicGeometry.Scheme.Opens.ι_appLE]
  show (Y.presheaf.map _ ≫ Y.presheaf.map _).hom y = y
  rw [← Functor.map_comp]
  have key : ∀ g : Opposite.op D ⟶ Opposite.op D, (Y.presheaf.map g).hom y = y := by
    intro g
    have hg : g = 𝟙 _ := Subsingleton.elim _ _
    rw [hg, CategoryTheory.Functor.map_id]
    rfl
  exact key _

/-- `appLE` of equal morphisms (the inclusion proof is transported). -/
theorem appLE_eq_of_eq {Y Z : AlgebraicGeometry.Scheme.{u}} {g g' : Y ⟶ Z} (h : g = g') (W : Z.Opens)
    (W' : Y.Opens) (e : W' ≤ g ⁻¹ᵁ W) (e' : W' ≤ g' ⁻¹ᵁ W) : g.appLE W W' e = g'.appLE W W' e' := by
  subst h; rfl

/-- `W ≤ U` in `C̃` gives `p_L⁻¹(W) ≤ p_L⁻¹(U)` (pointwise form). -/
theorem proj_preimage_mono_aux {W U : ρ.source.toScheme.Opens} (h : W ≤ U) :
    jetNeighborhood.proj L κ ⁻¹ᵁ W ≤ jetNeighborhood.proj L κ ⁻¹ᵁ U :=
  fun _ hx => h hx

/-- **Reading the pieces of `J` on `U`** from `J|_{p_L⁻¹U} = localJet Ψ`: for `n ≤ κ` and
`c ∈ B_V`, `J.pieceSection V n c |_U = pieceIso (π_n (Ψ c))`.

Proof: `pieceSection` is `Θ.app (ρ⁻¹V) (J^♯ c)` for the `𝒪`-linear map
`Θ := structureIso⁻¹ ≫ π_n ≫ pieceIso.hom : p_{L*}𝒪 → (L^∨)^{⊗n}` and `J^♯ c := J.hom.appLE (π⁻¹V) (p_L⁻¹ρ⁻¹V) c`;
by naturality (`PresheafOfModules.naturality_apply`) its restriction to `U` is `Θ.app U` of the
restriction of `J^♯ c` to `p_L⁻¹U`, which is `J.hom.appLE (π⁻¹V) (p_L⁻¹U) c` (`Scheme.Hom.appLE_map`)
`= topIso.hom ((p_L⁻¹U.ι ≫ J.hom).appLE (π⁻¹V) ⊤ c)` (`appLE_comp_appLE`, `Opens.ι_appLE`, `topIso_inv_apply`)
`= topIso.hom ((localJet Ψ).appLE (π⁻¹V) ⊤ c)` (`hJ`), and `structureIso⁻¹` of that is `Ψ c`
(`localJet_structureIso_inv`). -/
theorem pieceSection_of_localJet (J : BasedJet f ρ L κ)
    (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))
    (hJ : (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι ≫ J.hom = localJet f κ ρ L hV hU Ψ)
    (n : ℕ) (hn : n ≤ κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)) :
    ((AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).val.map
        (CategoryTheory.homOfLE hUV).op).hom (J.pieceSection V n hn c) =
      ((truncatedJetAlgebra.pieceIso L n).hom.val.app (Opposite.op U)).hom
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨n, Nat.lt_succ_of_le hn⟩).app U (Ψ.hom c)) := by
  -- the piece-extracting `𝒪`-linear map `Θ : p_{L*}𝒪 → (L^∨)^{⊗n}`
  set Θ : (AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
      (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n :=
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨n, Nat.lt_succ_of_le hn⟩ ≫ (truncatedJetAlgebra.pieceIso L n).hom with hΘ
  have e₁ : jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ V) ≤ J.hom ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage, J.over]
  have e₂ : jetNeighborhood.proj L κ ⁻¹ᵁ U ≤ J.hom ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) :=
    fun x hx => e₁ (proj_preimage_mono_aux κ ρ L hUV hx)
  have e₃ : (⊤ : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme.Opens) ≤
      (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ U) :=
    (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι_preimage_self.ge
  -- (1) naturality of `Θ` under restriction `U ≤ ρ⁻¹V`
  have h1 := PresheafOfModules.naturality_apply Θ.val (CategoryTheory.homOfLE hUV).op
    ((J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ V)) e₁).hom c)
  refine Eq.trans ?_ (congrArg (fun y => ((truncatedJetAlgebra.pieceIso L n).hom.val.app (Opposite.op U)).hom
    ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨n, Nat.lt_succ_of_le hn⟩).app U y)) (localJet_structureIso_inv f κ ρ L hV hU Ψ c))
  refine (h1.symm).trans ?_
  -- (2) the restricted section is `J^♯ c` on `p_L⁻¹U`, i.e. `topIso.hom ((ι ≫ J.hom)^♯ c)`
  have h2 : ((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
      (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).val.map (CategoryTheory.homOfLE hUV).op
        ((J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ V)) e₁).hom c) =
      (jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.hom.hom
        ((((jetNeighborhood.proj L κ ⁻¹ᵁ U).ι ≫ J.hom).appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤
          (fun x _ => e₂ ((jetNeighborhood.proj L κ ⁻¹ᵁ U).ι_preimage_self.ge trivial))).hom c) := by
    show ((jetNeighborhood L κ).left.presheaf.map (CategoryTheory.homOfLE (proj_preimage_mono_aux κ ρ L hUV)).op).hom
      ((J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ V)) e₁).hom c) = _
    have hb : ((jetNeighborhood L κ).left.presheaf.map (CategoryTheory.homOfLE (proj_preimage_mono_aux κ ρ L hUV)).op).hom
        ((J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ V)) e₁).hom c) =
        (J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) (jetNeighborhood.proj L κ ⁻¹ᵁ U) e₂).hom c :=
      congrArg (fun φ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
          Γ((jetNeighborhood L κ).left, jetNeighborhood.proj L κ ⁻¹ᵁ U) => φ.hom c)
        (AlgebraicGeometry.Scheme.Hom.appLE_map J.hom e₁
          (CategoryTheory.homOfLE (proj_preimage_mono_aux κ ρ L hUV)).op)
    rw [hb]
    have hc := congrArg (fun φ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
        Γ((jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme, ⊤) => φ.hom c)
      (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι J.hom
        ((MMSetup.cone f).hom ⁻¹ᵁ V) (jetNeighborhood.proj L κ ⁻¹ᵁ U) ⊤ e₂ e₃)
    exact (topIso_hom_ι_appLE_apply (jetNeighborhood.proj L κ ⁻¹ᵁ U) e₃ _).symm.trans
      (congrArg (jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.hom.hom hc)
  rw [h2]
  exact congrArg (fun m => (Θ.val.app (Opposite.op U)).hom ((jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.hom.hom m))
    (congrArg (fun φ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
        Γ((jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme, ⊤) => φ.hom c)
      (appLE_eq_of_eq hJ ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤ _ (top_le_localJet_preimage f κ ρ L hV hU Ψ)))

end jetNeighborhood

end
