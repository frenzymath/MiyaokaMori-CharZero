import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_RelSpecOverBase
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetSchemeWeightPieceSectionsRingHom

/-! # The local jet `p_L⁻¹(U) → 𝒵` attached to a ring map `B_V → 𝒜(U)`
(step 1 of the proof of Lemma 3.1 of the paper)

Over an affine open `U ⊆ C̃` the jet neighbourhood is affine, `p_L⁻¹(U) ≅ Spec 𝒜(U)` with
`𝒜(U) = ⊕_{q ≤ κ} L^{-q}(U)` (`relativeSpec.affineIso`), and over an affine open `V ⊆ C` the cone
is affine, `π⁻¹(V) ≅ Spec B_V` with `B_V = Γ(𝒵, π⁻¹V)` (`IsAffineHom.isAffine_preimage`). So a ring
homomorphism `Ψ : B_V → 𝒜(U)` gives a morphism `g_Ψ : p_L⁻¹(U) → 𝒵` ("the local jet"), and this module
records the three facts about it that the gluing needs: it lies over `ρ` when `Ψ` is compatible with
the structure maps (`localJet_over`), it is determined by `Ψ` — more precisely any two morphisms
`p_L⁻¹(U) → 𝒵` landing in `π⁻¹V` with the same `appLE` on `B_V` agree (`localJet_hom_ext`) — and `Ψ`
can be read back from `g_Ψ` through the structure isomorphism `𝒜 ≅ p_*𝒪` (`localJet_structureIso_inv`).
The zero-section condition (`localJet_zeroSection`) is the constant-term condition `π₀ ∘ Ψ = s^♯`.

In the paper the local jet is written in a frame, `(y, t) ↦ (ρ(y), (Σ_q a_{α,i,q}(y) t^q)_i)`; here
`Ψ` is the composite `B_V → 𝒪(U)[t]/(t^{κ+1}) → 𝒜(U)`, `t ↦ ι₁(μ)`, of a based affine jet with the
frame identification `truncatedJetAlgebra.quotToSections` — the frame enters only through `Ψ`.

-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace jetNeighborhood

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
  (L : LineBundle ρ.source.toVariety)

/-- The preimage of an affine open of `C` in the cone `𝒵` is affine (`π` is an affine morphism,
`MMSetup.cone_isAffineHom`). -/
theorem cone_preimage_isAffineOpen {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) :
    AlgebraicGeometry.IsAffineOpen ((MMSetup.cone f).hom ⁻¹ᵁ V) :=
  AlgebraicGeometry.IsAffineHom.isAffine_preimage V hV

/-- **The local jet** `g_Ψ : p_L⁻¹(U) → 𝒵` of a ring map `Ψ : B_V = Γ(𝒵, π⁻¹V) → 𝒜(U)`:
`p_L⁻¹(U) ≅ Spec 𝒜(U) → Spec B_V → π⁻¹V ↪ 𝒵` (`relativeSpec.affineIso`, `Spec.map Ψ`,
`IsAffineOpen.fromSpec`). -/
def localJet {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    {U : ρ.source.toScheme.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U)) :
    (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme ⟶ (MMSetup.cone f).left :=
  (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom ≫
    AlgebraicGeometry.Spec.map Ψ ≫ (cone_preimage_isAffineOpen f hV).fromSpec

variable {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
  {U : ρ.source.toScheme.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
  (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
    CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))

/-- The local jet lands in `π⁻¹V` (`IsAffineOpen.range_fromSpec`). -/
theorem top_le_localJet_preimage :
    (⊤ : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme.Opens) ≤
      localJet f κ ρ L hV hU Ψ ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) := by
  intro x _
  show (cone_preimage_isAffineOpen f hV).fromSpec.base ((AlgebraicGeometry.Spec.map Ψ).base
    ((AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom.base x)) ∈
    (MMSetup.cone f).hom ⁻¹ᵁ V
  exact (cone_preimage_isAffineOpen f hV).range_fromSpec.le ⟨_, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- **`over`**: if `Ψ` is compatible with the structure maps (`Ψ(π^♯ r) = ρ^♯ r · 1` for
`r ∈ Γ(C, V)`), then `g_Ψ ≫ π = p_L⁻¹(U).ι ≫ p_L ≫ ρ`.

Proof: `Spec.map Ψ ≫ fromSpec_{π⁻¹V} ≫ π = Spec.map Ψ ≫ Spec.map (π^♯) ≫ fromSpec_V`
(`IsAffineOpen.SpecMap_appLE_fromSpec`), `= Spec.map (sectionsUnit) ≫ Spec.map (ρ^♯) ≫ fromSpec_V`
by the hypothesis, `= Spec.map (sectionsUnit) ≫ fromSpec_U ≫ ρ` (`SpecMap_appLE_fromSpec` again), and
`affineIso.hom ≫ Spec.map (sectionsUnit) = (p_L ∣_ U) ≫ isoSpec.hom`
(`relativeSpec.affineIso_hom_Spec_map_sectionsUnit`), `isoSpec.hom ≫ fromSpec = U.ι`
(`isoSpec_inv_ι`), `(p_L ∣_ U) ≫ U.ι = p_L⁻¹(U).ι ≫ p_L` (`morphismRestrict_ι`). -/
theorem localJet_over (hUV : U ≤ ρ.hom ⁻¹ᵁ V)
    (hΨ : ∀ r : Γ(C.toScheme, V),
      Ψ.hom (((MMSetup.cone f).hom.appLE V ((MMSetup.cone f).hom ⁻¹ᵁ V) le_rfl).hom r) =
        (truncatedJetAlgebra L κ).sectionsUnit U ((ρ.hom.appLE V U hUV).hom r)) :
    localJet f κ ρ L hV hU Ψ ≫ (MMSetup.cone f).hom =
      (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι ≫ jetNeighborhood.proj L κ ≫ ρ.hom := by
  have hπV := cone_preimage_isAffineOpen f hV
  -- the ring map `B_V → 𝒜(U)` restricted to the constants is `sectionsUnit ∘ ρ^♯`
  have hcomp : (MMSetup.cone f).hom.appLE V ((MMSetup.cone f).hom ⁻¹ᵁ V) le_rfl ≫ Ψ =
      ρ.hom.appLE V U hUV ≫ CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsUnit U) := by
    ext r
    exact hΨ r
  -- `Spec.map Ψ ≫ fromSpec ≫ π = Spec.map (sectionsUnit) ≫ fromSpec_U ≫ ρ`
  have h1 : AlgebraicGeometry.Spec.map Ψ ≫ hπV.fromSpec ≫ (MMSetup.cone f).hom =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsUnit U)) ≫
        hU.fromSpec ≫ ρ.hom := by
    rw [← AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec (MMSetup.cone f).hom hV hπV le_rfl,
      ← Category.assoc, ← AlgebraicGeometry.Spec.map_comp, hcomp, AlgebraicGeometry.Spec.map_comp,
      Category.assoc, AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec ρ.hom hV hU hUV]
  -- `affineIso.hom ≫ Spec.map (sectionsUnit) ≫ fromSpec_U = p_L⁻¹(U).ι ≫ p_L`
  have h2 : (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsUnit U)) ≫
        hU.fromSpec = (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι ≫ jetNeighborhood.proj L κ := by
    rw [← Category.assoc,
      AlgebraicGeometry.Scheme.relativeSpec.affineIso_hom_Spec_map_sectionsUnit (truncatedJetAlgebra L κ)
        ⟨U, hU⟩, ← AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]
    exact AlgebraicGeometry.morphismRestrict_ι _ _
  show ((AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom ≫
    AlgebraicGeometry.Spec.map Ψ ≫ hπV.fromSpec) ≫ (MMSetup.cone f).hom = _
  rw [Category.assoc, Category.assoc, h1, ← Category.assoc, ← Category.assoc, ← Category.assoc, ← h2]
  simp only [Category.assoc]

include hV hU in
set_option backward.isDefEq.respectTransparency false in
/-- **Uniqueness**: two morphisms `p_L⁻¹(U) → 𝒵` landing in `π⁻¹V` with the same ring map on
`B_V = Γ(𝒵, π⁻¹V)` agree. Proof: transport along `affineIso : p_L⁻¹(U) ≅ Spec 𝒜(U)`; a morphism
`Spec 𝒜(U) → 𝒵` landing in the affine open `π⁻¹V` is `Spec.map (its appLE ≫ ΓSpecIso.hom) ≫ fromSpec`
(`IsAffineOpen.eq_SpecMap_appLE_fromSpec`), and `(affineIso.hom ≫ g).appLE = g.appLE ≫ affineIso.hom.appTop`
(`Scheme.Hom.appLE_comp_appLE`). -/
theorem localJet_hom_ext {g g' : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme ⟶ (MMSetup.cone f).left}
    (hg : (⊤ : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme.Opens) ≤ g ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V))
    (hg' : (⊤ : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme.Opens) ≤ g' ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V))
    (h : g.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤ hg = g'.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤ hg') :
    g = g' := by
  have hπV := cone_preimage_isAffineOpen f hV
  set e := AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩ with he
  -- any `g` landing in `π⁻¹V` is recovered from its ring map on `B_V`
  have key : ∀ (g : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme ⟶ (MMSetup.cone f).left)
      (hg : (⊤ : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme.Opens) ≤ g ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V)),
      g = e.hom ≫ AlgebraicGeometry.Spec.map
        ((g.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤ hg ≫ e.inv.appLE ⊤ ⊤ (fun _ _ => trivial)) ≫
          (AlgebraicGeometry.Scheme.ΓSpecIso _).hom) ≫ hπV.fromSpec := by
    intro g hg
    have e₁ : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))).Opens) ≤
        (e.inv ≫ g) ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) :=
      fun x _ => hg (x := e.inv.base x) trivial
    have h1 := hπV.eq_SpecMap_appLE_fromSpec (e.inv ≫ g) e₁
    rw [← AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE e.inv g _ ⊤ ⊤ hg (fun _ _ => trivial)] at h1
    exact (Iso.hom_inv_id_assoc e g).symm.trans (congrArg (fun m => e.hom ≫ m) h1)
  rw [key g hg, key g' hg', h]

/-- **Reading `Ψ` back**: the ring map of the local jet on `B_V` is `Ψ` followed by the identification
`𝒜(U) ≅ Γ(Spec 𝒜(U), ⊤) ≅ Γ(p_L⁻¹(U), ⊤)` (`IsAffineOpen.appLE_SpecMap_fromSpec`,
`Scheme.Hom.appLE_comp_appLE`). -/
theorem localJet_appLE :
    (localJet f κ ρ L hV hU Ψ).appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤
        (top_le_localJet_preimage f κ ρ L hV hU Ψ) =
      Ψ ≫ (AlgebraicGeometry.Scheme.ΓSpecIso _).inv ≫
        (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom.appTop := by
  have hπV := cone_preimage_isAffineOpen f hV
  set e := AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩ with he
  have e₁ : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))).Opens) ≤
      (AlgebraicGeometry.Spec.map Ψ ≫ hπV.fromSpec) ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) :=
    hπV.top_le_preimage_SpecMap_fromSpec Ψ
  have e₂ : (⊤ : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme.Opens) ≤ e.hom ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have h1 : (localJet f κ ρ L hV hU Ψ).appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤
      (top_le_localJet_preimage f κ ρ L hV hU Ψ) =
      (AlgebraicGeometry.Spec.map Ψ ≫ hπV.fromSpec).appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤ e₁ ≫
        e.hom.appLE ⊤ ⊤ e₂ :=
    (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE e.hom (AlgebraicGeometry.Spec.map Ψ ≫ hπV.fromSpec)
      ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤ ⊤ e₁ e₂).symm
  have h2 : e.hom.appLE ⊤ ⊤ e₂ = e.hom.appTop := by
    rw [AlgebraicGeometry.Scheme.Hom.appTop, AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
    rfl
  rw [h1, hπV.appLE_SpecMap_fromSpec Ψ e₁, h2, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **The jet through the structure isomorphism**: for `c ∈ B_V`, the section `g_Ψ^♯ c` of
`p_L⁻¹(U)`, viewed in `(p_{L*}𝒪)(U)`, is carried by `structureIso⁻¹ : p_{L*}𝒪 ≅ 𝒜` to `Ψ c`
(`relativeSpec.structureIso_inv_app_affine`, `sectionsIso`: the inverse is
`topIso⁻¹ ≫ (affineIso⁻¹)^♯ ≫ ΓSpecIso`, which undoes `localJet_appLE`). -/
theorem localJet_structureIso_inv (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)) :
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv.app U
      (show (((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
          (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).val.obj (Opposite.op U) : Type u) from
        (jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.hom.hom
          (((localJet f κ ρ L hV hU Ψ).appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤
            (top_le_localJet_preimage f κ ρ L hV hU Ψ)).hom c)) = Ψ.hom c := by
  set e := AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩ with he
  refine (AlgebraicGeometry.Scheme.relativeSpec.structureIso_inv_app_affine (truncatedJetAlgebra L κ)
    ⟨U, hU⟩ _).trans ?_
  have hA := congrArg (fun φ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      Γ((jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme, ⊤) => φ.hom c)
    (localJet_appLE f κ ρ L hV hU Ψ)
  simp only at hA
  rw [hA]
  -- unfold the inverse of `sectionsIso`: `topIso⁻¹ ≫ (affineIso⁻¹)^♯ ≫ ΓSpecIso`
  show (AlgebraicGeometry.Scheme.ΓSpecIso _).hom.hom (e.inv.appTop.hom
    (((jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.inv.hom ((jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.hom.hom
      (e.hom.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv.hom (Ψ.hom c))))))) = Ψ.hom c
  have h1 : ∀ x, (jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.inv.hom
      ((jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.hom.hom x) = x := fun x =>
    congrArg (fun φ : Γ((jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme, ⊤) ⟶
        Γ((jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme, ⊤) => φ.hom x)
      (jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.hom_inv_id
  have h2 : ∀ y, e.inv.appTop.hom (e.hom.appTop.hom y) = y := fun y => by
    have := congrArg (fun φ : Γ(AlgebraicGeometry.Spec (CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U)), ⊤) ⟶
        Γ(AlgebraicGeometry.Spec (CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U)), ⊤) => φ.hom y)
      ((AlgebraicGeometry.Scheme.Hom.comp_appTop e.inv e.hom).symm.trans
        (by rw [Iso.inv_hom_id, AlgebraicGeometry.Scheme.Hom.id_appTop]))
    exact this
  have h3 : ∀ z, (AlgebraicGeometry.Scheme.ΓSpecIso _).hom.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))).inv.hom z) = z :=
    fun z => congrArg (fun φ : CommRingCat.of _ ⟶ CommRingCat.of _ => φ.hom z)
      (AlgebraicGeometry.Scheme.ΓSpecIso _).inv_hom_id
  rw [h1, h2, h3]

end jetNeighborhood

end
