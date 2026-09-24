import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.AffineJetChartCoords
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetOfRingMap
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetGluing
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetInFrame
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.FrameJetCoefficientMap
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetIndependence
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.GluedJetWeightComponents
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.ParameterLineBundleRationalSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Frames
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame

/-! # The based jet of an affine jet from its regular normalized coefficients
(steps 3–5 of the proof of Lemma 3.1 of the paper)

> `a_{α,i,q} = γ^{-q} b_{α,i,q}` is regular … Replacing `ε` by `uε` replaces `γ` by `u^{-1}γ`,
> multiplies `a_{α,i,q}` by `u^q`, and changes the fiber coordinate from `t` to `u^{-1}t`. Thus the
> expressions `(y,t) ↦ (ρ(y), (Σ_q a_{α,i,q}(y) t^q)_i)`, `t^{k+1} = 0`, agree under changes of both
> the jet chart and the frame of `L`. In the relative étale coordinates centered at the seed, formal
> étaleness uniquely lifts them to `ȷ : C̃_(k)(L) → 𝒵`.

In this formalization the "expressions" are morphisms `p_L⁻¹(U) → 𝒵` obtained from the honest chart
`S(V α) ≅ Γ(V α)[x_{i,q}]` by `x_{i,q} ↦ a_{i,q}` (no formal étaleness is needed: `S(V α)` *is* the based
jet algebra `J_κ(B_α, s^♯)` of the cone, `relativeJetScheme.chartRing`, and its `O(U)`-points are the
based jets over `U`, `BasedJetAlgebra.homEquiv`). This module **assembles** the construction of `ȷ = J`
together with the identification of its weight components in every frame
(`exists_basedJet_of_regular_coefficients`) from the lemmas in the
modules `LocalJetOfRingMap` (the local jet `g_Ψ : p_L⁻¹U → 𝒵` of a ring map `Ψ : B_V → 𝒜(U)`),
`LocalJetInFrame` (`Ψ` in a frame: `quotToSections_μ ∘ homEquiv φ`, its pieces, structure map
and constant term, and the reading of the pieces of `J` from `J|_{p_L⁻¹U} = g_Ψ`),
`LocalJetGluing` (gluing over an affine cover of `C̃`, uniqueness over an affine cover, restriction of
the local jet, the zero-section condition), `FrameJetCoefficientMap` (the coefficient map `φ` of a
framed honest chart with its generic values), `LocalJetIndependence` (independence of the local
jet from chart and frame at the generic point) and `GluedJetWeightComponents` (weight components on the
chart coordinates). The per-point data of the construction is packaged in `LocalDatum`.

-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

namespace jetNeighborhood

variable (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
  (L : LineBundle ρ.source.toVariety) {ι : Type u} {V : ι → C.toScheme.Opens}
  (hV : ∀ α, AlgebraicGeometry.IsAffineOpen (V α))
  (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
    (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
  (hĵV : ∀ α, (⊤ : (AlgebraicGeometry.Spec
      (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
    ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V α))
  (s : L.toModules.stalk (genericPoint ρ.source.toScheme))

/-- **The per-point data of the construction**: an affine open `U ∋ η_{C̃}` inside `ρ⁻¹(V α)`, a frame
`e` of `L` on `U` with the coefficient `γ` of `s` in it and its dual frame `δ`, and the coefficient map
`φ : J_κ(B_{V α}, s^♯) → 𝒪(U)` with the generic values of `exists_algHom_of_honestChart`. -/
structure LocalDatum where
  α : ι
  U : ρ.source.toScheme.Opens
  hU : AlgebraicGeometry.IsAffineOpen U
  hηU : genericPoint ρ.source.toScheme ∈ U
  hUV : U ≤ ρ.hom ⁻¹ᵁ V α
  e : Γ(L.toModules, U)
  he : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules U e
  γ : ρ.source.toScheme.functionField
  hγ : s = γ • (L.toModules.presheaf.germ U (genericPoint ρ.source.toScheme) hηU e :
    L.toModules.stalk (genericPoint ρ.source.toScheme))
  δ : Γ(AlgebraicGeometry.Scheme.Modules.dual L.toModules, U)
  hδ : (AlgebraicGeometry.Scheme.Modules.dualEv L.toModules).app U
    (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
      L.toModules U δ e) = (1 : Γ(ρ.source.toScheme, U))
  φ : letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) (V α)
    letI := baseAlgebra ρ hUV
    coneJetAlgebra f κ (V α) →ₐ[Γ(C.toScheme, V α)] Γ(ρ.source.toScheme, U)
  hφ : ∀ (m : ℕ) (x : (jetAlgebra f κ).sectionsPiece (V α) m) (y : coneJetAlgebra f κ (V α)),
    (BasedJet.partι f κ m).val.app (Opposite.op (V α)) x = jetCoordinateSection f κ ⟨V α, hV α⟩ y →
    (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
     haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
     (ρ.source.toScheme.germToFunctionField U).hom (φ y)) =
      γ ^ (-(m : ℤ)) * affineJetCoord ρ ĵ (hĵV α) m x

namespace LocalDatum

variable {f κ ρ L hV ĵ hĵV s} (D : LocalDatum f κ ρ L hV ĵ hĵV s)

/-- The frame `μ = zpowNegOneIso⁻¹ δ` of `L^{-1}` on `U` (the fibre coordinate `t`). -/
def μ : Γ((L.zpow (-1)).toModules, D.U) := L.zpowNegOneIso.inv.app D.U D.δ

theorem hμ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules D.U D.μ :=
  (AlgebraicGeometry.Scheme.Modules.IsFrame.dual_of_pairing_eq_one D.hδ).map_iso L.zpowNegOneIso.symm

/-- The ring map `Ψ : B_{V α} → 𝒜(U)` of the datum. -/
def Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V D.α) ⟶
    CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing D.U) :=
  frameJetRingMap f κ ρ L D.hUV D.μ D.φ

/-- The local jet `g_Ψ : p_L⁻¹(U) → 𝒵` of the datum. -/
def g : (jetNeighborhood.proj L κ ⁻¹ᵁ D.U).toScheme ⟶ (MMSetup.cone f).left :=
  localJet f κ ρ L (hV D.α) D.hU D.Ψ

theorem over_Ψ (r : Γ(C.toScheme, V D.α)) :
    D.Ψ.hom (((MMSetup.cone f).hom.appLE (V D.α) ((MMSetup.cone f).hom ⁻¹ᵁ V D.α) le_rfl).hom r) =
      (truncatedJetAlgebra L κ).sectionsUnit D.U ((ρ.hom.appLE (V D.α) D.U D.hUV).hom r) :=
  frameJetRingMap_over f κ ρ L D.hUV D.μ D.φ r

theorem zero_Ψ (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V D.α)) :
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩).app D.U (D.Ψ.hom c) =
      (ρ.hom.appLE (V D.α) D.U D.hUV).hom
        (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V D.α) (V D.α)
          (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 (V D.α))).hom c) :=
  frameJetRingMap_π_zero f κ ρ L D.hUV D.μ D.φ c

/-- The generic value of the positive-weight pieces of `Ψ`: `(π_{q+1}(Ψ c))_η = (γ^{-(q+1)} · (d_q c)(ĵ)) • (μ^{⊗(q+1)})_η`
(`frameJetRingMap_π`, `PresheafOfModules.germ_smul`, `hφ` on the jet coordinate `d_q c`,
`exists_part_eq_jetCoordinate`). -/
theorem gen_Ψ (q : Fin κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V D.α)) :
    ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ D.U (genericPoint ρ.source.toScheme) D.hηU
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨(q : ℕ) + 1, Nat.succ_lt_succ q.2⟩).app D.U (D.Ψ.hom c)) :
      (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)) =
    (D.γ ^ (-((q : ℕ) + 1 : ℤ)) * affineJetCoeff f κ ρ ĵ (hV D.α) (hĵV D.α) ((q : ℕ) + 1) c) •
      ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ D.U (genericPoint ρ.source.toScheme) D.hηU
        (truncatedJetAlgebra.framePow L D.U D.μ ((q : ℕ) + 1)) :
      (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)) := by
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) (V D.α)
  haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  haveI : Nonempty D.U := ⟨⟨_, D.hηU⟩⟩
  have hπ := frameJetRingMap_π f κ ρ L D.hUV D.μ D.φ ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2) c
  show (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ D.U (genericPoint ρ.source.toScheme) D.hηU
    ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨(q : ℕ) + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt q.2)⟩).app D.U
        ((frameJetRingMap f κ ρ L D.hUV D.μ D.φ).hom c)) = _
  rw [hπ]
  refine (PresheafOfModules.germ_smul (R := ρ.source.toScheme.presheaf)
    (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).val (genericPoint ρ.source.toScheme) D.U D.hηU _ _).trans ?_
  congr 1
  obtain ⟨x, hx⟩ := BasedJet.exists_part_eq_jetCoordinate f κ ⟨V D.α, hV D.α⟩ q c
    (relativeJetScheme.hom_preimage_chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
      ⟨V D.α, hV D.α⟩)
  have h1 := D.hφ ((q : ℕ) + 1) x _ hx
  exact h1.trans (congrArg (fun t => D.γ ^ (-((q : ℕ) + 1 : ℤ)) * t)
    (congrArg (affineJetValue f κ ρ ĵ (hĵV D.α)) hx))

/-- Two data agree on every affine `W ≤ U₁ ⊓ U₂` containing `η` (`localJet_eq_of_generic` with the frame
relation `frameChange_zpow_smul_germ_framePow`). -/
theorem compat (D₁ D₂ : LocalDatum f κ ρ L hV ĵ hĵV s)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {W : ρ.source.toScheme.Opens} (hW : AlgebraicGeometry.IsAffineOpen W)
    (hηW : genericPoint ρ.source.toScheme ∈ W) (hW₁ : W ≤ D₁.U) (hW₂ : W ≤ D₂.U) :
    (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L hW₁) ≫ D₁.g =
      (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L hW₂) ≫ D₂.g :=
  localJet_eq_of_generic f κ ρ L ĵ hĵ (hV D₁.α) (hV D₂.α) (hĵV D₁.α) (hĵV D₂.α) D₁.hU D₂.hU D₁.hηU D₂.hηU
    D₁.hUV D₂.hUV D₁.μ D₁.hμ D₂.μ D₂.hμ D₁.γ D₂.γ
    (fun n => frameChange_zpow_smul_germ_framePow ρ L D₂.hηU D₁.hηU D₂.e D₂.he D₁.e D₁.he D₂.δ D₂.hδ
      D₁.δ D₁.hδ s D₂.γ D₁.γ D₂.hγ D₁.hγ n)
    D₁.Ψ D₂.Ψ D₁.over_Ψ D₂.over_Ψ D₁.zero_Ψ D₂.zero_Ψ D₁.gen_Ψ D₂.gen_Ψ hW hηW hW₁ hW₂

end LocalDatum

end jetNeighborhood

set_option linter.unusedVariables false in
/-- **The based jet of an affine jet with regular normalized coefficients, and its weight components
in a frame** (Lemma 3.1 of the paper). Data: a finite cover `ρ : C̃ → C`;
a `κ(η_{C̃})`-point `ĵ` of the affine jet scheme `J_κ^s` over `η_{C̃} ≫ ρ` (`hĵ`); a family of affine
honest jet charts `(V α, chart α)` covering `C`, each containing the image of `ĵ` (`hĵV`); the tuples
`b α i q = ĵ^♯(x^α_{i,q})` (`hb`, `affineJetCoord`); a line bundle `L` on `C̃` with an element `s` of its
stalk at `η_{C̃}` (the rational section `s_L`); and the **regularity hypothesis** `hreg`: for every affine
open `U ∋ η_{C̃}` inside some `ρ⁻¹(V α)`, every frame `e` of `L` on `U` and the coefficient `γ` with
`s = γ • e_η`, all normalized coefficients `a^{α,e}_{i,q} := γ^{-(q+1)} b α i q` are germs of sections
`r ∈ O(U)`. Conclusion: there is a based jet `J : C̃_(κ)(L) → 𝒵` over `ρ` such that, for every such
`(U, α, e, γ)`, every `δ ∈ Γ(U, L^∨)` with `⟨δ, e⟩ = 1` (the dual frame, so that `μ := zpowNegOneIso⁻¹ δ`
is the frame `ε^∨` of `L^{-1}` and `t = μ` is the fiber coordinate of `trivialization_of_frame`) and
every `r ∈ O(U)` with germ `a^{α,e}_{i,q}`:
`Ψ_{q+1}(x^α_{i,q})|_U = r • μ^{⊗(q+1)}`, where `Ψ_m := J.weightComponent m` transposed along the
adjunction to `S_m(V α) → Γ(ρ⁻¹V α, (L^∨)^{⊗m})` and `μ^{⊗m} := pieceIso (framePow μ m)`.

Natural-language proof (notation: `S := jetAlgebra f κ`, `𝒵 := MMSetup.cone f`, `s₀ := MMSetup.seed f`,
`B_α := Γ(𝒵, π⁻¹(V α))`, `J_κ^s := relativeJetScheme 𝒵 s₀ κ`, `p := jetNeighborhood.proj L κ`).
1. **The local jets.** Let `(U, α, e, γ)` be as in `hreg`, `hU : IsAffineOpen U`, `δ` the dual frame
   (`IsFrame.exists_dual_pairing_one_dualEv e`), `μ := zpowNegOneIso.inv δ`, and
   `a_{i,q} ∈ O(U)` the sections given by `hreg` (unique, `germToFunctionField_injective`).
   `trivialization_of_frame`  gives `e_U : p⁻¹(U) ≅ Spec O(U)[t]/(t^{κ+1})`
   over `U`, with `t ↦ ι_1(μ)`. The honest chart gives `ε_α : S(V α) ≃+* Γ(V α)[x_p]`
   (`(chart α).honest`), and `S(V α) = J_κ(B_α, s₀^♯) = relativeJetScheme.chartRing … (V α)` (via
   `relativeJetScheme.chartSections`,  uses this
   identification). Let `φ_U : S(V α) → O(U)` be the `Γ(V α)`-algebra map (structure map
   `Γ(V α) → O(U)` induced by `ρ`, as `U ≤ ρ⁻¹V α`) with `φ_U(x^α_{i,q}) = a_{i,q}`, i.e. `φ_U = ev_a ∘ ε_α`.
   Under `BasedJetAlgebra.homEquiv`  it corresponds to a ring map
   `ψ_U : B_α → O(U)[t]/(t^{κ+1})` over `Γ(V α) → O(U)` with constant term `s₀^♯`, i.e.
   (`𝒵|_{V α} = Spec B_α` is affine over `V α`, `MMSetup.cone_isAffineHom`; `p⁻¹(U)` is affine by `e_U`)
   to a morphism `g_U : p⁻¹(U) → 𝒵` with `g_U ≫ π = p⁻¹(U).ι ≫ p ≫ ρ` and `g_U` restricting to
   `ρ ≫ s₀` on the zero section `t = 0` (`jetNeighborhood.zeroSection`, `JetZeroSection`: on
   `Spec O(U)[t]/(t^{κ+1})` the zero section is `t ↦ 0`, and the constant term of `ψ_U` is `s₀^♯`).
   Equivalently, `g_U` is `relativeJetScheme.toBasedJet` of the `C`-morphism `U → Spec S(V α) → J_κ^s`
   given by `φ_U` (`relativeJetScheme.chart`, `RelativeJetRepresentableByCharts`), transported along
   `e_U` and `jetThickening U ≅ Spec O(U)[t]/(t^{κ+1})`.
2. **Independence of `(α, e)`.** For two such data `(U, α, e, γ)`, `(U, β, e', γ')` on the same
   affine `U`, the two `O(U)`-points of `J_κ^s` agree: `O(U) → K(C̃)` is injective (`U` nonempty open of
   the integral `C̃`), so it suffices to compare after composing with `K(C̃)`, where both ring maps
   `S(V α ⊓ V β) → K(C̃)` are `x ↦ γ^{-m} ĵ^♯(x)` on `S_m` **after the coordinate change** `t ↦ u⁻¹ t`:
   precisely, `e' = u • e` with `u ∈ O(U)^×` (`IsFrame.isUnit_coord`), `γ' = γ u⁻¹`
   (`normalized_coefficients_frame_change`), `μ' = u⁻¹ μ`, and the
   two based jets `B → O(U)[t]/(t^{κ+1})` differ by the substitution `t ↦ u t` composed with the
   rescaling of coefficients `a' = u^{q+1} a` — which cancel (`jetRescaling`,
   `GmActionGradingCorrespondence`: the `G_m`-action on `J_κ^s` scales `x_{i,q}` by `λ^{q+1}` and `t` by
   `λ⁻¹`). The chart change `α → β` is the identity of `S(V α ⊓ V β)` written in two presentations
   (`hb`: both tuples are `ĵ^♯` of the respective coordinates, `AffineJetChartTransition`). Hence the
   morphisms `g_U` depend only on `U` (they are `g_U = p⁻¹(U).ι ≫ J.hom` for the `J` to be built).
3. **Gluing.** Cover `C̃` by affine opens `U_j` with `U_j ≤ ρ⁻¹(V α_j)` (`hcover`) and a frame of `L`
   on `U_j` (`Modules.exists_affine_frame_le`); `𝒰 := {p⁻¹(U_j)}` is an open
   cover of `C̃_(κ)(L)` (`Scheme.openCoverOfIsOpenCover`). On `p⁻¹(U_i ⊓ U_j)` (affine, `C̃` separated)
   both `g_{U_i}` and `g_{U_j}` restrict to the morphism of step 1 for `U_i ⊓ U_j` with the restricted
   frames (restriction of a based jet is the based jet of the restricted data:
   `relativeJetScheme.representableBy_homEquiv_comp`, `BasedJetOpenRestriction`), so they agree by
   step 2 (`hcompat`); `hover`, `hrestrict` are step 1. `exists_glued_jet`  gives
   `J : BasedJet f ρ L κ` with `p⁻¹(U_j).ι ≫ J.hom = g_{U_j}`; and for an arbitrary `(U, α, e, γ)` as in
   the conclusion, `p⁻¹(U).ι ≫ J.hom = g_U` by the same restriction argument on `U ⊓ U_j`
   (morphisms into the separated `𝒵` over `C` agreeing on an open cover agree).
4. **Weight components.** Fix `(U, α, e, γ)`, `δ`, `μ`, `(i, q)`, `r` as in the conclusion; then
   `r = a_{i,q}` (`germToFunctionField_injective`). Write `x := x^α_{i,q} ∈ S_{q+1}(V α)` as a
   polynomial in the generators `d_{q'} c` (`BasedJetAlgebra.coeffClass`, `c ∈ B_α`) of the based jet
   algebra through `ε_α⁻¹` and `relativeJetScheme.chartSections`. For a generator,
   `BasedJet.weightComponent_jetCoordinate`  gives
   `Ψ_{q'+1}(d_{q'} c) = J.pieceSection (V α) (q'+1) c`, the `t^{q'+1}`-coefficient of `J^♯ c`; on `U`,
   `J^♯ c = g_U^♯ c = ψ_U(c)` (step 3 and the construction of `g_U`), whose `t^{q'+1}`-coefficient is
   `φ_U(d_{q'} c) · μ^{⊗(q'+1)}` (`BasedJetAlgebra.lift_coeffClass`: `homEquiv` reads coefficients;
   `pieceSection` reads the `ξ`-expansion along `structureIso`, and under `e_U` the piece `L^{-m}` is
   `O(U) · t^m` with `t = μ`, `truncatedJetAlgebra.quotToSections_mk_X`). `Ψ` is multiplicative and
   `Γ(V α)`-linear (`BasedJet.weightComponent_map_mul`, `weightComponent_map_one`), so for the polynomial `x`: `Ψ_{q+1}(x)|_U = φ_U(x) · μ^{⊗(q+1)}
   = a_{i,q} • μ^{⊗(q+1)}`, where `μ^{⊗m}` is `pieceIso (framePow μ m)` (`framePow_succ`,
   `tensorSections`, the multiplication of `truncatedJetAlgebra` is `pieceMul`). ∎

**Assembly.** The per-point data `(U, α, e, γ, δ, φ)` is
the record `jetNeighborhood.LocalDatum`; `φ` comes from `exists_algHom_of_honestChart`
(`FrameJetCoefficientMap`: the coefficient map of the framed chart with its generic values, step 1)
applied to the sections given by `hreg`. Step 1's local jet is `LocalDatum.g = localJet (frameJetRingMap μ φ)`
(`LocalJetOfRingMap`, `LocalJetInFrame`: `over`, uniqueness, `appLE`, the constant term
`frameJetRingMap_π_zero` and the pieces `frameJetRingMap_π`); its zero-section condition is
`localJet_zeroSection` (`LocalJetGluing`). Step 2 is `LocalDatum.compat`, i.e. `localJet_eq_of_generic`
with the frame relation `frameChange_zpow_smul_germ_framePow` (`LocalJetIndependence`) applied to the
generic values `LocalDatum.gen_Ψ` (proved here from `frameJetRingMap_π`, `hφ` and
`exists_part_eq_jetCoordinate`). Step 3 is `exists_glued_jet_of_affineOpens` on the cover `(D y).U`, and the
identification `J|_{p_L⁻¹U} = D₀.g` for an arbitrary framed chart datum `D₀` uses `hom_ext_of_affineOpens`
over affine `W_z ≤ U ⊓ (D z).U` and `compat` again (`LocalJetGluing`). Step 4 is
`weightComponent_of_localJet` (`GluedJetWeightComponents`) for the representative `y` of `x^α_{i,q}`
(`jetCoordinateSection_surjective`), and `r = φ y` because both have the germ `γ^{-(q+1)} b α i q`
(`germToFunctionField_injective`, `hb`).

Edge cases: `κ = 0`: `Fin 0` is empty, `J` is the seed jet `p ≫ ρ ≫ s₀`, the conclusion is vacuous;
`s = 0` is allowed (then `γ = 0` for every frame, `hreg` forces `r = 0` and `J` is again the seed jet
— the statement stays true, no hypothesis `s ≠ 0` is needed); `U` must be affine only to apply
`trivialization_of_frame`. The hypotheses `hV`, `hηV` are those of the parent and are not all used. -/
theorem exists_basedJet_of_regular_coefficients [IsAlgClosed k]
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {ι : Type u} {V : ι → C.toScheme.Opens} (hV : ∀ α, AlgebraicGeometry.IsAffineOpen (V α))
    (chart : ∀ α, HonestJetChart f κ (V α)) (hηV : ∀ α, genericPoint C.toScheme ∈ V α)
    (hcover : ∀ c : C.toScheme, ∃ α, c ∈ V α)
    (hĵV : ∀ α, (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V α))
    (b : ι → Fin (X.toVariety.dim + 1) → Fin κ → ρ.source.toScheme.functionField)
    (hb : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      b α i q = affineJetCoord ρ ĵ (hĵV α) _ ((chart α).coords (i, q)))
    (L : LineBundle ρ.source.toVariety) (s : L.toModules.stalk (genericPoint ρ.source.toScheme))
    (hreg : ∀ (U : ρ.source.toScheme.Opens) (_ : AlgebraicGeometry.IsAffineOpen U)
      (hηU : genericPoint ρ.source.toScheme ∈ U) (α : ι) (_ : U ≤ ρ.hom ⁻¹ᵁ V α)
      (e : Γ(L.toModules, U)) (_ : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules U e)
      (γ : ρ.source.toScheme.functionField),
      s = γ • (L.toModules.presheaf.germ U (genericPoint ρ.source.toScheme) hηU e :
        L.toModules.stalk (genericPoint ρ.source.toScheme)) →
      ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ), ∃ r : Γ(ρ.source.toScheme, U),
        (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
         haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
         (ρ.source.toScheme.germToFunctionField U).hom r) = γ ^ (-((q : ℕ) + 1 : ℤ)) * b α i q) :
    ∃ J : BasedJet f ρ L κ,
      ∀ (U : ρ.source.toScheme.Opens) (_ : AlgebraicGeometry.IsAffineOpen U)
        (hηU : genericPoint ρ.source.toScheme ∈ U) (α : ι) (hUV : U ≤ ρ.hom ⁻¹ᵁ V α)
        (e : Γ(L.toModules, U)) (_ : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules U e)
        (γ : ρ.source.toScheme.functionField),
        s = γ • (L.toModules.presheaf.germ U (genericPoint ρ.source.toScheme) hηU e :
          L.toModules.stalk (genericPoint ρ.source.toScheme)) →
        ∀ (δ : Γ(AlgebraicGeometry.Scheme.Modules.dual L.toModules, U)),
          (AlgebraicGeometry.Scheme.Modules.dualEv L.toModules).app U
            (AlgebraicGeometry.Scheme.Modules.tensorSections
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules) L.toModules U δ e) =
            (1 : Γ(ρ.source.toScheme, U)) →
        ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ) (r : Γ(ρ.source.toScheme, U)),
          (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
           haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
           (ρ.source.toScheme.germToFunctionField U).hom r) = γ ^ (-((q : ℕ) + 1 : ℤ)) * b α i q →
          (show Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
              (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩), U) from
            ((AlgebraicGeometry.Scheme.Modules.monoidalPow
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
              (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).val.map (CategoryTheory.homOfLE hUV).op).hom
            (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _)
              (J.weightComponent (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩))).val.app
                (Opposite.op (V α))).hom ((chart α).coords (i, q)))) =
            r • (show Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
              (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩), U) from
              (((truncatedJetAlgebra.pieceIso L (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).hom.val.app
                (Opposite.op U)).hom
                (truncatedJetAlgebra.framePow L U (L.zpowNegOneIso.inv.app U δ)
                  (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)))) := by
  classical
  haveI hInt : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  -- the coefficient map of a framed chart at any datum `(U, α, e, γ)`
  have hlocal : ∀ (U : ρ.source.toScheme.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
      (hηU : genericPoint ρ.source.toScheme ∈ U) (α : ι) (hUV : U ≤ ρ.hom ⁻¹ᵁ V α)
      (e : Γ(L.toModules, U)) (he : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules U e)
      (γ : ρ.source.toScheme.functionField),
      s = γ • (L.toModules.presheaf.germ U (genericPoint ρ.source.toScheme) hηU e :
        L.toModules.stalk (genericPoint ρ.source.toScheme)) →
      ∃ φ : (letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) (V α)
          letI := jetNeighborhood.baseAlgebra ρ hUV
          jetNeighborhood.coneJetAlgebra f κ (V α) →ₐ[Γ(C.toScheme, V α)] Γ(ρ.source.toScheme, U)),
        ∀ (m : ℕ) (x : (jetAlgebra f κ).sectionsPiece (V α) m) (y : jetNeighborhood.coneJetAlgebra f κ (V α)),
          (BasedJet.partι f κ m).val.app (Opposite.op (V α)) x =
            jetNeighborhood.jetCoordinateSection f κ ⟨V α, hV α⟩ y →
          (haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
           (ρ.source.toScheme.germToFunctionField U).hom (φ y)) =
            γ ^ (-(m : ℤ)) * affineJetCoord ρ ĵ (hĵV α) m x := by
    intro U hU hηU α hUV e he γ hγ
    choose a ha using fun i q => hreg U hU hηU α hUV e he γ hγ i q
    exact jetNeighborhood.exists_algHom_of_honestChart f κ ρ (chart α) ĵ hĵ (hĵV α) hU hηU hUV γ a
      (fun i q => (ha i q).trans (congrArg (fun t => γ ^ (-((q : ℕ) + 1 : ℤ)) * t) (hb α i q)))
  -- a local datum at every point of `C̃`
  have hcov' : ∀ y : ρ.source.toScheme, ∃ D : jetNeighborhood.LocalDatum f κ ρ L hV ĵ hĵV s, y ∈ D.U := by
    intro y
    obtain ⟨α, hyα⟩ := hcover (ρ.hom.base y)
    have hy' : y ∈ ρ.hom ⁻¹ᵁ V α := hyα
    obtain ⟨U, hU, hUV, hyU, e, he⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le L.toModules hy'
    have hηU : genericPoint ρ.source.toScheme ∈ U :=
      (genericPoint_specializes y).mem_open U.isOpen hyU
    obtain ⟨γ, hγ⟩ := he.exists_smul_germ_eq hηU s
    obtain ⟨δ, hδ⟩ := he.exists_dual_pairing_one_dualEv
    obtain ⟨φ, hφ⟩ := hlocal U hU hηU α hUV e he γ hγ
    exact ⟨⟨α, U, hU, hηU, hUV, e, he, γ, hγ, δ, hδ, φ, hφ⟩, hyU⟩
  choose D hD using hcov'
  -- glue the local jets
  obtain ⟨J, hJ⟩ := jetNeighborhood.exists_glued_jet_of_affineOpens f κ ρ L (fun y => (D y).U)
    (fun y => (D y).hU) (fun y => ⟨y, hD y⟩) (fun y => (D y).g)
    (fun y => jetNeighborhood.localJet_over f κ ρ L (hV (D y).α) (D y).hU (D y).Ψ (D y).hUV (D y).over_Ψ)
    (fun y => jetNeighborhood.localJet_zeroSection f κ ρ L (hV (D y).α) (D y).hU (D y).hUV (D y).Ψ (D y).zero_Ψ)
    (fun y z W hW hηW hy hz => (D y).compat (D z) hĵ hW hηW hy hz)
  refine ⟨J, ?_⟩
  intro U hU hηU α hUV e he γ hγ δ hδ i q r hr
  obtain ⟨φ, hφ⟩ := hlocal U hU hηU α hUV e he γ hγ
  let D₀ : jetNeighborhood.LocalDatum f κ ρ L hV ĵ hĵV s := ⟨α, U, hU, hηU, hUV, e, he, γ, hγ, δ, hδ, φ, hφ⟩
  -- `J` restricted to `p_L⁻¹U` is the local jet of `D₀`
  have hJU : (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι ≫ J.hom = D₀.g := by
    have hcovU : ∀ z : U, ∃ W : ρ.source.toScheme.Opens,
        AlgebraicGeometry.IsAffineOpen W ∧ (z : ρ.source.toScheme) ∈ W ∧ W ≤ U ⊓ (D z).U := by
      intro z
      obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWle⟩ :=
        ρ.source.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
          (show (z : ρ.source.toScheme) ∈ (U ⊓ (D z).U : ρ.source.toScheme.Opens) from ⟨z.2, hD z⟩)
          (U ⊓ (D z).U).isOpen
      exact ⟨W, hW, hzW, hWle⟩
    choose W hW using hcovU
    refine jetNeighborhood.hom_ext_of_affineOpens f κ ρ L W (fun z => (hW z).2.2.trans inf_le_left)
      (fun y hy => ⟨⟨y, hy⟩, (hW ⟨y, hy⟩).2.1⟩) (fun z => ?_)
    have hηW : genericPoint ρ.source.toScheme ∈ W z :=
      (genericPoint_specializes (z : ρ.source.toScheme)).mem_open (W z).isOpen (hW z).2.1
    have hWD : W z ≤ (D z).U := (hW z).2.2.trans inf_le_right
    have hWU : W z ≤ U := (hW z).2.2.trans inf_le_left
    calc (jetNeighborhood L κ).left.homOfLE (jetNeighborhood.proj_preimage_mono κ ρ L hWU) ≫
          (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι ≫ J.hom
        = (jetNeighborhood.proj L κ ⁻¹ᵁ W z).ι ≫ J.hom := by
          rw [← Category.assoc, AlgebraicGeometry.Scheme.homOfLE_ι]
      _ = (jetNeighborhood L κ).left.homOfLE (jetNeighborhood.proj_preimage_mono κ ρ L hWD) ≫
          (jetNeighborhood.proj L κ ⁻¹ᵁ (D z).U).ι ≫ J.hom := by
          rw [← Category.assoc, AlgebraicGeometry.Scheme.homOfLE_ι]
      _ = (jetNeighborhood L κ).left.homOfLE (jetNeighborhood.proj_preimage_mono κ ρ L hWD) ≫ (D z).g := by
          rw [hJ]
      _ = (jetNeighborhood L κ).left.homOfLE (jetNeighborhood.proj_preimage_mono κ ρ L hWU) ≫ D₀.g :=
          (D z).compat D₀ hĵ (hW z).1 hηW hWD hWU
  -- the weight component of the chart coordinate
  obtain ⟨y, hy⟩ := jetNeighborhood.jetCoordinateSection_surjective f κ ⟨V α, hV α⟩
    ((BasedJet.partι f κ (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).val.app (Opposite.op (V α))
      ((chart α).coords (i, q)))
  have hΨ := jetNeighborhood.weightComponent_of_localJet f κ ρ L J (hV α) hU hUV D₀.μ D₀.hμ φ hJU
    (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩) ((chart α).coords (i, q)) y hy.symm
  -- `φ y = r`: both have the germ `γ^{-(q+1)} b α i q`
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hφy : φ y = r := by
    apply ρ.source.toScheme.germToFunctionField_injective U
    show (ρ.source.toScheme.germToFunctionField U).hom (φ y) = (ρ.source.toScheme.germToFunctionField U).hom r
    rw [hφ _ _ y hy.symm, hr, hb α i q]
    rfl
  rw [← hφy]
  exact hΨ

end
