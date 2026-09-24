import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.GlueJet
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetOfRingMap

/-! # Gluing local jets over an affine open cover of `C̃`
(step 3 of the proof of Lemma 3.1 of the paper)

`exists_glued_jet`  glues morphisms `g_i : 𝒰.X i → 𝒵` given on an open cover `𝒰` of
`C̃_(κ)(L)` with compatibilities stated on fibre products. The local jets of the construction live on
the opens `p_L⁻¹(U_j)` for an affine cover `(U_j)` of `C̃`, and their compatibility is naturally
verified on affine opens `W ≤ U_i ⊓ U_j` (where the two local jets are both `jetNeighborhood.localJet`
of the restricted data, `localJet_restrict`). This module translates between the two forms:

* `exists_glued_jet_of_affineOpens`: the gluing statement for `(p_L⁻¹(U_j))_j`, compatibilities on
  affine `W ≤ U_i ⊓ U_j`, and the zero-section condition in the form
  `(zeroSection ∣_ p_L⁻¹U_j) ≫ g_j = (zeroSection⁻¹ p_L⁻¹U_j).ι ≫ ρ ≫ s`;
* `hom_ext_of_affineOpens`: two morphisms `p_L⁻¹(U) → 𝒵` agreeing on `p_L⁻¹(W_j)` for affine `W_j ≤ U`
  covering `U` agree (used to identify `J|_{p_L⁻¹U}` with the local jet of an arbitrary framed chart);
* `localJet_restrict`: the local jet of `Ψ` restricted to `p_L⁻¹(W)`, `W ≤ U` affine, is the local jet
  of `Ψ` followed by restriction `𝒜(U) → 𝒜(W)`;
* `localJet_zeroSection`: the zero-section condition for the local jet is the constant-term condition
  `π₀ ∘ Ψ = s^♯` (via `zeroSection_restrict_affineIso`: over `U` the zero section is `Spec` of the
  augmentation `π₀ : 𝒜(U) → 𝒪(U)`, and `isAffine_hom_ext_of_appLE`).
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

/-- `W ≤ U` in `C̃` gives `p_L⁻¹(W) ≤ p_L⁻¹(U)`. -/
theorem proj_preimage_mono {W U : ρ.source.toScheme.Opens} (h : W ≤ U) :
    jetNeighborhood.proj L κ ⁻¹ᵁ W ≤ jetNeighborhood.proj L κ ⁻¹ᵁ U :=
  fun _ hx => h hx

/-- **Morphisms from an affine scheme into an affine open are determined by their ring map**:
`a b : Y ⟶ Z` with `Y` affine, both landing in the affine open `V ⊆ Z`, and with the same
`appLE V ⊤`, are equal (`IsAffineOpen.eq_SpecMap_appLE_fromSpec` transported along `Y.isoSpec`;
same argument as `localJet_hom_ext`). -/
theorem isAffine_hom_ext_of_appLE {Y Z : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    {V : Z.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) {a b : Y ⟶ Z}
    (ha : (⊤ : Y.Opens) ≤ a ⁻¹ᵁ V) (hb : (⊤ : Y.Opens) ≤ b ⁻¹ᵁ V)
    (h : a.appLE V ⊤ ha = b.appLE V ⊤ hb) : a = b := by
  have key : ∀ (a : Y ⟶ Z) (ha : (⊤ : Y.Opens) ≤ a ⁻¹ᵁ V),
      a = Y.isoSpec.hom ≫ AlgebraicGeometry.Spec.map
        ((a.appLE V ⊤ ha ≫ Y.isoSpec.inv.appLE ⊤ ⊤ (fun _ _ => trivial)) ≫
          (AlgebraicGeometry.Scheme.ΓSpecIso _).hom) ≫ hV.fromSpec := by
    intro a ha
    have e₁ : (⊤ : (AlgebraicGeometry.Spec Γ(Y, ⊤)).Opens) ≤ (Y.isoSpec.inv ≫ a) ⁻¹ᵁ V :=
      fun x _ => ha (x := Y.isoSpec.inv.base x) trivial
    have h1 := hV.eq_SpecMap_appLE_fromSpec (Y.isoSpec.inv ≫ a) e₁
    rw [← AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE Y.isoSpec.inv a _ ⊤ ⊤ ha (fun _ _ => trivial)] at h1
    exact (Iso.hom_inv_id_assoc Y.isoSpec a).symm.trans (congrArg (fun m => Y.isoSpec.hom ≫ m) h1)
  rw [key a ha, key b hb, h]

/-- **Gluing over an affine cover of `C̃`** ( in the form used by the construction;
Stacks 01JJ / Mathlib `Scheme.OpenCover.glueMorphisms`). Data: affine opens `U_j` covering `C̃`,
morphisms `g_j : p_L⁻¹(U_j) → 𝒵` over `ρ` (`hover`), restricting to `ρ ≫ s` along the zero section
(`hrestrict`, stated with the restriction `zeroSection ∣_ p_L⁻¹U_j : zeroSection⁻¹(p_L⁻¹U_j) → p_L⁻¹U_j`),
and agreeing on `p_L⁻¹(W)` for every affine `W ≤ U_i ⊓ U_j` containing the generic point (`hcompat`;
every nonempty open of the irreducible `C̃` contains `η_{C̃}`, `genericPoint_specializes`, so this is
no restriction). Conclusion: a based jet `J` with `p_L⁻¹(U_j).ι ≫ J.hom = g_j`.

Proof (as formalized). Let `𝒰 := Cover.mkOfCovers (p_L⁻¹(U_j))` (a cover because `p_L` is
surjective onto the `U_j`'s union `C̃`: `x ∈ p_L⁻¹(U_j)` for the `j` with `p_L(x) ∈ U_j`). Apply
`exists_glued_jet` to `𝒰` and `g`:
* `hover` is `hover` (`𝒰.f j = (p_L⁻¹U_j).ι` definitionally);
* `hcompat` on the fibre product `P := p_L⁻¹U_i ×_{C̃_(κ)L} p_L⁻¹U_j`: cover `P` by the maps
  `pullback.lift (homOfLE) (homOfLE) : p_L⁻¹(W) → P` for affine `W ≤ U_i ⊓ U_j` containing `η`
  (open immersions by `IsOpenImmersion.of_comp` since `lift ≫ fst = homOfLE`; jointly surjective: a
  point `x ∈ P` has `p_L(ι(fst x)) ∈ U_i ⊓ U_j`, take an affine `W` around it (`isBasis_affineOpens`),
  it contains `η` because it is a nonempty open of the irreducible `C̃` (`genericPoint_specializes`),
  and `lift ⟨ι(fst x), _⟩ = x` by injectivity of `fst`); on each piece both composites are
  `homOfLE ≫ g` (`pullback.lift_fst/snd`), equal by `hcompat W`; conclude with `Scheme.Cover.hom_ext`;
* `hrestrict`: the fibre product `C̃ ×_{C̃_(κ)L} p_L⁻¹U_j ≅ zeroSection⁻¹(p_L⁻¹U_j)`
  (`pullbackRestrictIsoRestrict (zeroSection L κ) (p_L⁻¹U_j)`), under which `pullback.snd` is
  `zeroSection ∣_ p_L⁻¹U_j` (by definition of `morphismRestrict`) and `pullback.fst` is
  `(zeroSection⁻¹ p_L⁻¹U_j).ι` (`pullbackRestrictIsoRestrict_inv_fst`); so `hrestrict j` is the required
  equation after cancelling the epimorphism `iso.inv`.
The hypothesis `hW` (affineness of the `U_j`) is not used by the proof; it is kept because the assembly
in `BasedJetOfRegularCoefficients` supplies it and the statement is fixed there. Edge cases: `ι'` empty is excluded by
`hcov` (`C̃` is nonempty); `κ = 0` fine. -/
theorem exists_glued_jet_of_affineOpens [IsAlgClosed k] {ι' : Type u}
    (W : ι' → ρ.source.toScheme.Opens) (hW : ∀ j, AlgebraicGeometry.IsAffineOpen (W j))
    (hcov : ∀ y : ρ.source.toScheme, ∃ j, y ∈ W j)
    (g : ∀ j, (jetNeighborhood.proj L κ ⁻¹ᵁ W j).toScheme ⟶ (MMSetup.cone f).left)
    (hover : ∀ j, g j ≫ (MMSetup.cone f).hom =
      (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι ≫ jetNeighborhood.proj L κ ≫ ρ.hom)
    (hrestrict : ∀ j, (jetNeighborhood.zeroSection L κ ∣_ (jetNeighborhood.proj L κ ⁻¹ᵁ W j)) ≫ g j =
      (jetNeighborhood.zeroSection L κ ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ W j)).ι ≫ ρ.hom ≫
        (MMSetup.seed f).1)
    (hcompat : ∀ i j (U : ρ.source.toScheme.Opens), AlgebraicGeometry.IsAffineOpen U →
      genericPoint ρ.source.toScheme ∈ U → ∀ (hi : U ≤ W i) (hj : U ≤ W j),
      (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L hi) ≫ g i =
        (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L hj) ≫ g j) :
    ∃ J : BasedJet f ρ L κ, ∀ j, (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι ≫ J.hom = g j := by
  -- the open cover of `C̃_(κ)(L)` by the `p_L⁻¹(W j)`
  have hcov' : ∀ x : (jetNeighborhood L κ).left, ∃ j,
      ∃ y : (jetNeighborhood.proj L κ ⁻¹ᵁ W j).toScheme, (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι y = x := by
    intro x
    obtain ⟨j, hj⟩ := hcov (jetNeighborhood.proj L κ x)
    exact ⟨j, ⟨x, hj⟩, rfl⟩
  let 𝒰 : (jetNeighborhood L κ).left.OpenCover :=
    AlgebraicGeometry.Scheme.Cover.mkOfCovers ι' (fun j => (jetNeighborhood.proj L κ ⁻¹ᵁ W j).toScheme)
      (fun j => (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι) hcov'
  -- compatibility on the fibre products, checked on the cover by `p_L⁻¹(U)`, `U` affine ∋ η
  have hcompat' : ∀ i j : ι',
      pullback.fst (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι ≫ g i =
      pullback.snd (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι ≫ g j := by
    intro i j
    let J := {U : ρ.source.toScheme.Opens // AlgebraicGeometry.IsAffineOpen U ∧
      genericPoint ρ.source.toScheme ∈ U ∧ U ≤ W i ∧ U ≤ W j}
    let lift : ∀ U : J, (jetNeighborhood.proj L κ ⁻¹ᵁ U.1).toScheme ⟶
        pullback (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι := fun U =>
      pullback.lift ((jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L U.2.2.2.1))
        ((jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L U.2.2.2.2))
        (by rw [AlgebraicGeometry.Scheme.homOfLE_ι, AlgebraicGeometry.Scheme.homOfLE_ι])
    have hlift_fst : ∀ U : J, lift U ≫ pullback.fst _ _ =
        (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L U.2.2.2.1) :=
      fun U => pullback.lift_fst _ _ _
    have hlift_snd : ∀ U : J, lift U ≫ pullback.snd _ _ =
        (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L U.2.2.2.2) :=
      fun U => pullback.lift_snd _ _ _
    haveI hoi : ∀ U : J, AlgebraicGeometry.IsOpenImmersion (lift U) := fun U => by
      haveI : AlgebraicGeometry.IsOpenImmersion (lift U ≫ pullback.fst
          (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι) := by
        rw [hlift_fst]; infer_instance
      exact AlgebraicGeometry.IsOpenImmersion.of_comp (lift U) (pullback.fst _ _)
    have hcovP : ∀ x : (pullback (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι
        (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι : AlgebraicGeometry.Scheme.{u}),
        ∃ U : J, ∃ y, lift U y = x := by
      intro x
      have hzi : jetNeighborhood.proj L κ (pullback.fst (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι
          (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι x).1 ∈ W i :=
        (pullback.fst (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι x).2
      have hz' : (pullback.snd (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι
          (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι x).1 = (pullback.fst (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι
          (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι x).1 := by
        show (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι (pullback.snd (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι
            (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι x) =
          (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι (pullback.fst (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι
            (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι x)
        rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, ← AlgebraicGeometry.Scheme.Hom.comp_apply,
          pullback.condition]
      have hzj : jetNeighborhood.proj L κ (pullback.fst (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι
          (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι x).1 ∈ W j := by
        rw [← hz']
        exact (pullback.snd (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι x).2
      have hmem : jetNeighborhood.proj L κ (pullback.fst (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι
          (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι x).1 ∈ W i ⊓ W j := ⟨hzi, hzj⟩
      obtain ⟨U, hUaff, hUmem, hUle⟩ :=
        Opens.isBasis_iff_nbhd.mp ρ.source.toScheme.isBasis_affineOpens hmem
      have hUaff' : AlgebraicGeometry.IsAffineOpen U := hUaff
      have hη : genericPoint ρ.source.toScheme ∈ U :=
        (genericPoint_specializes _).mem_open U.2 hUmem
      obtain ⟨y, hy⟩ : ∃ y : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme,
          (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι y = (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι
            (pullback.fst (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι x) :=
        ⟨⟨_, hUmem⟩, rfl⟩
      refine ⟨⟨U, hUaff', hη, hUle.trans inf_le_left, hUle.trans inf_le_right⟩, y, ?_⟩
      apply (pullback.fst (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι
        (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι).isOpenEmbedding.injective
      rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, hlift_fst]
      exact Subtype.ext ((AlgebraicGeometry.Scheme.homOfLE_apply _ _).trans hy)
    let 𝒱 : (pullback (jetNeighborhood.proj L κ ⁻¹ᵁ W i).ι (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι).OpenCover :=
      AlgebraicGeometry.Scheme.Cover.mkOfCovers J (fun U => (jetNeighborhood.proj L κ ⁻¹ᵁ U.1).toScheme)
        lift hcovP
    refine AlgebraicGeometry.Scheme.Cover.hom_ext 𝒱 _ _ (fun (U : J) => ?_)
    show lift U ≫ pullback.fst _ _ ≫ g i = lift U ≫ pullback.snd _ _ ≫ g j
    rw [← Category.assoc, hlift_fst, ← Category.assoc, hlift_snd]
    exact hcompat i j U.1 U.2.1 U.2.2.1 U.2.2.2.1 U.2.2.2.2
  -- the zero-section condition on the fibre product
  have hrestrict' : ∀ j : ι',
      pullback.snd (jetNeighborhood.zeroSection L κ) (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι ≫ g j =
      pullback.fst (jetNeighborhood.zeroSection L κ) (jetNeighborhood.proj L κ ⁻¹ᵁ W j).ι ≫ ρ.hom ≫
        (MMSetup.seed f).1 := by
    intro j
    rw [← cancel_epi (AlgebraicGeometry.pullbackRestrictIsoRestrict (jetNeighborhood.zeroSection L κ)
      (jetNeighborhood.proj L κ ⁻¹ᵁ W j)).inv, ← Category.assoc, ← Category.assoc,
      AlgebraicGeometry.pullbackRestrictIsoRestrict_inv_fst]
    exact hrestrict j
  obtain ⟨J, hJ⟩ := exists_glued_jet f κ ρ L 𝒰 g hcompat' hover hrestrict'
  exact ⟨J, hJ⟩

/-- **Uniqueness over an affine cover of `U`**: two morphisms `p_L⁻¹(U) → 𝒵` that agree after
restriction to `p_L⁻¹(W_j)`, for affine opens `W_j ≤ U` covering `U`, are equal.

Proof: the morphisms `homOfLE : p_L⁻¹(W_j) → p_L⁻¹(U)` are open immersions and jointly surjective
(`p_L(x) ∈ W_j` for some `j`), so they form an open cover of `p_L⁻¹(U)` (`Scheme.Cover.mkOfCovers`), and
`Scheme.Cover.hom_ext` gives the claim. -/
theorem hom_ext_of_affineOpens {U : ρ.source.toScheme.Opens} {ι' : Type u}
    (W : ι' → ρ.source.toScheme.Opens) (hWU : ∀ j, W j ≤ U) (hcov : ∀ y ∈ U, ∃ j, y ∈ W j)
    {g g' : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme ⟶ (MMSetup.cone f).left}
    (h : ∀ j, (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L (hWU j)) ≫ g =
      (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L (hWU j)) ≫ g') :
    g = g' := by
  have hcov' : ∀ x : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme, ∃ j,
      ∃ y : (jetNeighborhood.proj L κ ⁻¹ᵁ W j).toScheme,
      (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L (hWU j)) y = x := by
    intro x
    obtain ⟨j, hj⟩ := hcov _ x.2
    exact ⟨j, ⟨x.1, hj⟩, Subtype.ext (AlgebraicGeometry.Scheme.homOfLE_apply _ _)⟩
  let 𝒰 : (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme.OpenCover :=
    AlgebraicGeometry.Scheme.Cover.mkOfCovers ι'
      (fun j => (jetNeighborhood.proj L κ ⁻¹ᵁ W j).toScheme)
      (fun j => (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L (hWU j))) hcov'
  exact AlgebraicGeometry.Scheme.Cover.hom_ext 𝒰 g g' h

set_option backward.isDefEq.respectTransparency false in
/-- **Restriction of the local jet** to a smaller affine open `W ≤ U`: it is the local jet of
`Ψ` followed by the restriction `𝒜(U) → 𝒜(W)`.

Proof (as formalized): unfolding `localJet`, it suffices that the charts of the relative Spec are
compatible with restriction, `homOfLE ≫ affineIso_U.hom = affineIso_W.hom ≫ Spec.map (res)`; this follows
from `relativeSpec.affineIso_inv_ι` (`affineIso⁻¹ ≫ ι = chart`) and `QCAlgebra.specMap_chart`
(`Spec.map (res) ≫ chart U = chart W`, Stacks 01LQ) after cancelling the monomorphisms `affineIso_U.inv`
and `(p_L⁻¹U).ι`, together with `Scheme.homOfLE_ι`. -/
theorem localJet_restrict {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    {U W : ρ.source.toScheme.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (hW : AlgebraicGeometry.IsAffineOpen W) (hWU : W ≤ U)
    (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U)) :
    (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L hWU) ≫ localJet f κ ρ L hV hU Ψ =
      localJet f κ ρ L hV hW
        (Ψ ≫ CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsRestrict hWU)) := by
  -- the charts are compatible with restriction: `homOfLE ≫ eU.hom = eW.hom ≫ Spec.map res`
  have hchart : (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L hWU) ≫
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom =
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsRestrict hWU)) := by
    rw [← cancel_mono (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).inv,
      ← cancel_mono ((AlgebraicGeometry.Scheme.relativeSpec (truncatedJetAlgebra L κ)).hom ⁻¹ᵁ U).ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have h1 := AlgebraicGeometry.Scheme.relativeSpec.affineIso_inv_ι (truncatedJetAlgebra L κ) ⟨U, hU⟩
    have h2 := AlgebraicGeometry.Scheme.relativeSpec.affineIso_inv_ι (truncatedJetAlgebra L κ) ⟨W, hW⟩
    have h3 : AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsRestrict hWU)) ≫
        (truncatedJetAlgebra L κ).toAffineAlgebra.chart ⟨U, hU⟩ =
        (truncatedJetAlgebra L κ).toAffineAlgebra.chart ⟨W, hW⟩ :=
      AlgebraicGeometry.Scheme.QCAlgebra.specMap_chart (truncatedJetAlgebra L κ)
        (U := ⟨U, hU⟩) (V := ⟨W, hW⟩) hWU
    have h4 : ((AlgebraicGeometry.Scheme.relativeSpec (truncatedJetAlgebra L κ)).hom ⁻¹ᵁ W).ι =
        (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩).hom ≫
          (truncatedJetAlgebra L κ).toAffineAlgebra.chart ⟨W, hW⟩ := by
      rw [← h2, Iso.hom_inv_id_assoc]
    have h5 : (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L hWU) ≫
        (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι = (jetNeighborhood.proj L κ ⁻¹ᵁ W).ι :=
      (jetNeighborhood L κ).left.homOfLE_ι _
    rw [h1]
    exact h5.trans (h4.trans (congrArg (fun m =>
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩).hom ≫ m) h3.symm))
  show ((jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L hWU) ≫
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom) ≫
      AlgebraicGeometry.Spec.map Ψ ≫ (cone_preimage_isAffineOpen f hV).fromSpec =
    (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩).hom ≫
      AlgebraicGeometry.Spec.map (Ψ ≫ CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsRestrict hWU)) ≫
      (cone_preimage_isAffineOpen f hV).fromSpec
  rw [hchart, AlgebraicGeometry.Spec.map_comp]
  simp only [Category.assoc]

/-- `zeroSection⁻¹(p_L⁻¹U) = U` (`zeroSection ≫ p_L = 𝟙`). -/
theorem zeroSection_preimage_proj_preimage (U : ρ.source.toScheme.Opens) :
    jetNeighborhood.zeroSection L κ ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ U) = U := by
  show (jetNeighborhood.zeroSection L κ ≫ jetNeighborhood.proj L κ) ⁻¹ᵁ U = U
  rw [jetNeighborhood.zeroSection_proj]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The zero section over an affine open `U`, composed with the chart `p_L⁻¹U ≅ Spec 𝒜(U)`, is
`Spec` of the augmentation `π₀ : 𝒜(U) → 𝒪(U)`: `(isoOfEq ≫ zeroSection ∣_ p_L⁻¹U) ≫ affineIso.hom =
U.toSpecΓ ≫ Spec.map π₀` (`ι_ofAlgebraMap_left`, `affineIso_inv_ι`, cancel the mono `chart U`). -/
theorem zeroSection_restrict_affineIso {U : ρ.source.toScheme.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    (ρ.source.toScheme.isoOfEq (zeroSection_preimage_proj_preimage κ ρ L U).symm).hom ≫
      (jetNeighborhood.zeroSection L κ ∣_ (jetNeighborhood.proj L κ ⁻¹ᵁ U)) ≫
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom =
    U.toSpecΓ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((truncatedJetAlgebra L κ).algebraMapSections _ (jetNeighborhood.augmentation L κ)
        (jetNeighborhood.augmentation_isAlgebraMap L κ) U)) := by
  have h1 : (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).inv ≫
      (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι = (truncatedJetAlgebra L κ).toAffineAlgebra.chart ⟨U, hU⟩ :=
    AlgebraicGeometry.Scheme.relativeSpec.affineIso_inv_ι (truncatedJetAlgebra L κ) ⟨U, hU⟩
  have h2 : U.ι ≫ jetNeighborhood.zeroSection L κ =
      U.toSpecΓ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        ((truncatedJetAlgebra L κ).algebraMapSections _ (jetNeighborhood.augmentation L κ)
          (jetNeighborhood.augmentation_isAlgebraMap L κ) U)) ≫
        (truncatedJetAlgebra L κ).toAffineAlgebra.chart ⟨U, hU⟩ :=
    AlgebraicGeometry.Scheme.relativeSpec.ι_ofAlgebraMap_left (truncatedJetAlgebra L κ)
      (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id ρ.source.toScheme))
      (jetNeighborhood.augmentation L κ) (jetNeighborhood.augmentation_isAlgebraMap L κ) ⟨U, hU⟩
  have hL : ((ρ.source.toScheme.isoOfEq (zeroSection_preimage_proj_preimage κ ρ L U).symm).hom ≫
      (jetNeighborhood.zeroSection L κ ∣_ (jetNeighborhood.proj L κ ⁻¹ᵁ U)) ≫
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom) ≫
      ((AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).inv ≫
        (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι) = U.ι ≫ jetNeighborhood.zeroSection L κ := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [AlgebraicGeometry.morphismRestrict_ι, ← Category.assoc,
      AlgebraicGeometry.Scheme.isoOfEq_hom_ι]
  have hR : (U.toSpecΓ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((truncatedJetAlgebra L κ).algebraMapSections _ (jetNeighborhood.augmentation L κ)
        (jetNeighborhood.augmentation_isAlgebraMap L κ) U))) ≫
      ((AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).inv ≫
        (jetNeighborhood.proj L κ ⁻¹ᵁ U).ι) = U.ι ≫ jetNeighborhood.zeroSection L κ := by
    rw [h2, h1]
    simp only [Category.assoc]
  exact (cancel_mono _).mp (hL.trans hR.symm)

set_option backward.isDefEq.respectTransparency false in
/-- **The zero-section condition for the local jet** (Lemma 3.1 of the paper: "`ȷ` restricts to `s ∘ ρ` on
the zero section"; §3 of the paper): if the constant term of `Ψ` is `s^♯`, i.e.
`π₀ (Ψ c) = ρ^♯ (s^♯ c)` for all `c ∈ B_V` (`π₀ : 𝒜(U) → 𝒪(U)` the projection to the weight-`0`
piece), then `g_Ψ` composed with the zero section `C̃ → C̃_(κ)(L)` (restricted over `p_L⁻¹U`) is
`ρ ≫ s`.

Proof (as formalized). `zeroSection⁻¹(p_L⁻¹U) = U` as opens of `C̃` (`zeroSection ≫ p_L = 𝟙`,
`zeroSection_preimage_proj_preimage`), so after precomposing with the isomorphism `isoOfEq : U ≅
zeroSection⁻¹(p_L⁻¹U)` both sides are morphisms `U → 𝒵` from the affine scheme `U` landing in the affine
open `π⁻¹V`; by `isAffine_hom_ext_of_appLE` it suffices to compare their ring maps `B_V → Γ(U, ⊤)`
(`appLE (π⁻¹V) ⊤`) on each `c ∈ B_V`:
* right side: `(U.ι ≫ ρ ≫ s).appLE (π⁻¹V) ⊤ c = res_{U→⊤} (ρ^♯ (s^♯ c))` (`appLE_comp_appLE` twice,
  `Scheme.Opens.ι_appLE`);
* left side: `((isoOfEq ≫ zeroSection ∣_ p_L⁻¹U) ≫ localJet Ψ).appLE (π⁻¹V) ⊤ c =
  (y₁ ≫ affineIso.hom).appTop (ΓSpecIso⁻¹ (Ψ c))` (`appLE_comp_appLE`, `localJet_appLE`, `comp_appTop`), and
  `y₁ ≫ affineIso.hom = U.toSpecΓ ≫ Spec.map π₀` (`zeroSection_restrict_affineIso`: the zero section is
  `ofAlgebraMap augmentation`, whose chart formula `ι_ofAlgebraMap_left` gives `U.ι ≫ zeroSection =
  U.toSpecΓ ≫ Spec.map (algebraMapSections augmentation U) ≫ chart U`, and `chart U = affineIso⁻¹ ≫ ι`);
  so the left side is `topIso⁻¹ (π₀ (Ψ c))` (`ΓSpecIso_inv_naturality`, `Opens.toSpecΓ_appTop`,
  `algebraMapSections` evaluates to `augmentation.app U = π₀.app U` definitionally).
The hypothesis `hΨ0` identifies the two, and `U.ι.appLE U ⊤ = U.topIso.inv` (`ι_appLE`).
Edge cases: `κ = 0` (`𝒜 = 𝒪`, `π₀ = id`, `g_Ψ = ρ ≫ s` on the nose); `U = ⊥` trivial. -/
theorem localJet_zeroSection {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    {U : ρ.source.toScheme.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) (hUV : U ≤ ρ.hom ⁻¹ᵁ V)
    (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))
    (hΨ0 : ∀ c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V),
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩).app U (Ψ.hom c) =
        (ρ.hom.appLE V U hUV).hom
          (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
            (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c)) :
    (jetNeighborhood.zeroSection L κ ∣_ (jetNeighborhood.proj L κ ⁻¹ᵁ U)) ≫ localJet f κ ρ L hV hU Ψ =
      (jetNeighborhood.zeroSection L κ ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ U)).ι ≫ ρ.hom ≫ (MMSetup.seed f).1 := by
  have hπV := cone_preimage_isAffineOpen f hV
  haveI : AlgebraicGeometry.IsAffine U.toScheme := hU
  -- transport the source along `U ≅ zeroSection⁻¹(p_L⁻¹U)`
  rw [← cancel_epi (ρ.source.toScheme.isoOfEq (zeroSection_preimage_proj_preimage κ ρ L U).symm).hom,
    AlgebraicGeometry.Scheme.isoOfEq_hom_ι_assoc]
  conv_lhs => rw [← Category.assoc]
  -- notation for the restricted zero section `U → p_L⁻¹U`
  set y₁ : U.toScheme ⟶ (jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme :=
    (ρ.source.toScheme.isoOfEq (zeroSection_preimage_proj_preimage κ ρ L U).symm).hom ≫
      (jetNeighborhood.zeroSection L κ ∣_ (jetNeighborhood.proj L κ ⁻¹ᵁ U)) with hy₁
  have hle : U ≤ (ρ.hom ≫ (MMSetup.seed f).1) ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) := fun x hx =>
    relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V (hUV hx)
  have ha : (⊤ : U.toScheme.Opens) ≤ (y₁ ≫ localJet f κ ρ L hV hU Ψ) ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) :=
    fun x _ => top_le_localJet_preimage f κ ρ L hV hU Ψ (x := y₁.base x) trivial
  have hb : (⊤ : U.toScheme.Opens) ≤ (U.ι ≫ ρ.hom ≫ (MMSetup.seed f).1) ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) :=
    fun x _ => hle x.2
  refine isAffine_hom_ext_of_appLE hπV ha hb ?_
  ext c
  -- left side: through `localJet_appLE` and the chart computation of the zero section
  have e₂ : (⊤ : U.toScheme.Opens) ≤ y₁ ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hL1 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE y₁ (localJet f κ ρ L hV hU Ψ)
    ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤ ⊤ (top_le_localJet_preimage f κ ρ L hV hU Ψ) e₂
  have hL2 : y₁.appLE ⊤ ⊤ e₂ = y₁.appTop := by
    rw [AlgebraicGeometry.Scheme.Hom.appTop, AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
    rfl
  have hL3 := zeroSection_restrict_affineIso κ ρ L hU
  rw [← Category.assoc] at hL3
  -- right side: `appLE` of the composite `U.ι ≫ ρ ≫ s`
  have e₄ : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun x _ => x.2
  have hR1 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE U.ι (ρ.hom ≫ (MMSetup.seed f).1)
    ((MMSetup.cone f).hom ⁻¹ᵁ V) U ⊤ hle e₄
  have hR2 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE ρ.hom (MMSetup.seed f).1
    ((MMSetup.cone f).hom ⁻¹ᵁ V) V U
    (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) hUV
  rw [← hL1, ← hR1, ← hR2, hL2, localJet_appLE f κ ρ L hV hU Ψ]
  simp only [CommRingCat.comp_apply]
  rw [← hΨ0 c]
  -- normalise the applications
  show y₁.appTop.hom
      ((AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom.appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))).inv.hom
          (Ψ.hom c))) =
    (U.ι.appLE U ⊤ e₄).hom
      ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩).app U (Ψ.hom c))
  -- LHS: `y₁ ≫ affineIso.hom = U.toSpecΓ ≫ Spec.map π₀`
  have hL4 : ∀ w, y₁.appTop.hom
      ((AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨U, hU⟩).hom.appTop.hom w) =
      U.toSpecΓ.appTop.hom ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        ((truncatedJetAlgebra L κ).algebraMapSections _ (jetNeighborhood.augmentation L κ)
          (jetNeighborhood.augmentation_isAlgebraMap L κ) U))).appTop.hom w) := by
    intro w
    have := congrArg (fun m => (AlgebraicGeometry.Scheme.Hom.appTop m).hom w) hL3
    simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at this
    exact this
  rw [hL4]
  -- `Spec.map φ` on global sections is `φ` under `ΓSpecIso`
  have hL5 : ∀ z, (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        ((truncatedJetAlgebra L κ).algebraMapSections _ (jetNeighborhood.augmentation L κ)
          (jetNeighborhood.augmentation_isAlgebraMap L κ) U))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))).inv.hom z) =
      (AlgebraicGeometry.Scheme.ΓSpecIso _).inv.hom
        ((truncatedJetAlgebra L κ).algebraMapSections _ (jetNeighborhood.augmentation L κ)
          (jetNeighborhood.augmentation_isAlgebraMap L κ) U z) := fun z =>
    (congrArg (fun ψ : CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U) ⟶ _ => ψ.hom z)
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
        ((truncatedJetAlgebra L κ).algebraMapSections _ (jetNeighborhood.augmentation L κ)
          (jetNeighborhood.augmentation_isAlgebraMap L κ) U)))).symm
  rw [hL5]
  -- `U.toSpecΓ` on global sections undoes `ΓSpecIso` and lands in `Γ(U, ⊤)` via `topIso.inv`
  have hL6 : ∀ z, U.toSpecΓ.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(ρ.source.toScheme, U)).inv.hom z) =
      U.topIso.inv.hom z := by
    intro z
    have := congrArg (fun ψ => ψ.hom ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(ρ.source.toScheme, U)).inv.hom z))
      (AlgebraicGeometry.Scheme.Opens.toSpecΓ_appTop U)
    rw [this]
    exact congrArg (fun ψ : Γ(ρ.source.toScheme, U) ⟶ Γ(U.toScheme, ⊤) => ψ.hom z)
      (Iso.inv_hom_id_assoc (AlgebraicGeometry.Scheme.ΓSpecIso Γ(ρ.source.toScheme, U)) U.topIso.inv)
  show U.toSpecΓ.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(ρ.source.toScheme, U)).inv.hom
      ((truncatedJetAlgebra L κ).algebraMapSections _ (jetNeighborhood.augmentation L κ)
        (jetNeighborhood.augmentation_isAlgebraMap L κ) U (Ψ.hom c))) = _
  rw [hL6]
  -- both sides are the restriction `Γ(C̃, U) → Γ(U, ⊤)` of `π₀ (Ψ c)`
  have hfin : U.ι.appLE U ⊤ e₄ = U.topIso.inv := by
    rw [AlgebraicGeometry.Scheme.Opens.ι_appLE]
    rfl
  rw [hfin]
  rfl

end jetNeighborhood

end
