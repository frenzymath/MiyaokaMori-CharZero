import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesPowLocallyFree
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProductResidueFieldPoint
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionInPunctured
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivNaturality
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt

/-! # Vanishing of all tautological coordinates forces a point into the zero section

Statement. `V = A^{⊕(N+1)}` (`A` a line bundle on a scheme `X`), `p : Tot(V) → X` the total space,
`τ := totalSpaceHomEquiv V (Tot V) (𝟙)` ∈ Γ(Tot V, p^*V) the
tautological section and `τ_ℓ := p^*(π_ℓ)(τ)` ∈ Γ(Tot V, p^*A) its coordinates. If every `τ_ℓ`
vanishes at a point `v ∈ Tot(V)` (`IsZeroAt`), then `v` lies in the image
of the zero section `σ₀ := zeroSection V`:
`mem_range_zeroSection_of_forall_isZeroAt_coordinate`.
This is the pointwise form of "Z^× = Z ∖ σ₀(C) is where the coordinates are not all zero"
(Definition 2.1 of the paper); it is the converse of
`seedSection.totSection_apply_ne_zeroSection_apply`, and the same
fact (for the trivial bundle over `Spec k`) is what `puncturedAffineConeCoord_not_all_isZeroAt` needs.

Two transport lemmas accompany it:
* `totalSpaceHomEquiv_naturality_map`: for any module map `π : V ⟶ L`, precomposing an `X`-morphism
  `m : T → Tot V` with `j : S → T.left` and taking the `π`-coordinate of the corresponding section
  equals pulling back the `π`-coordinate of `m`'s section along `j` (then `pullbackComp`). This is
  `totalSpaceHomEquiv_naturality_coordinate` with the
  biproduct projection replaced by an arbitrary `π`; same proof.
* `isZeroAt_tautological_coordinate_of_isZeroAt`: if `j : S → Tot V` lies over `q : S → X`
  (`j ≫ p = q`) and the `π`-coordinate of the section corresponding to `j` vanishes at `w ∈ S`, then
  the `π`-coordinate of the tautological section vanishes at `j(w)`. Proof: `subst`, the naturality
  above, `isZeroAt_map` for the inverse of `pullbackComp`, and
  `isZeroAt_of_isZeroAt_sectionPullbackAlong`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Coordinate naturality of `totalSpaceHomEquiv` for an arbitrary module map `π : V ⟶ L`
(generalizes `totalSpaceHomEquiv_naturality_coordinate`, which is the case `π = biproduct.π`). -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_map {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {L : X.Modules} (π : V ⟶ L)
    (T : CategoryTheory.Over X) {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T.left)
    (m : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    (((AlgebraicGeometry.Scheme.Modules.pullback (j ≫ T.hom)).map π).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (j ≫ T.hom))
          ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m))
      = (((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app L).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong j
            ((((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map π).val.app
              (Opposite.op ⊤)).hom (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T m))) := by
  rw [AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality, sectionPullbackAlong_naturality]
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.naturality π
  exact (congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom
    (sectionPullbackAlong j (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T m))) h).symm

/-- If `j : S → Tot V` lies over `q` and the `π`-coordinate of the section of `q^*V` corresponding
to `j` vanishes at `w`, then the `π`-coordinate of the tautological section vanishes at `j w`. -/
theorem isZeroAt_tautological_coordinate_of_isZeroAt {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {L : X.Modules} (π : V ⟶ L)
    {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left)
    (q : S ⟶ X) (hq : j ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = q) (w : S)
    (h : IsZeroAt ((((AlgebraicGeometry.Scheme.Modules.pullback q).map π).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk q)
        (CategoryTheory.Over.homMk j hq))) w) :
    IsZeroAt ((((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace V).hom).map π).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
        (CategoryTheory.CategoryStruct.id _))) (j.base w) := by
  subst hq
  have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_map V π
    (AlgebraicGeometry.Scheme.totalSpace V) j (𝟙 _)
  rw [Category.comp_id] at hn
  rw [hn] at h
  let τπ := (((AlgebraicGeometry.Scheme.Modules.pullback
    (AlgebraicGeometry.Scheme.totalSpace V).hom).map π).val.app (Opposite.op ⊤)).hom
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V) (𝟙 _))
  let Θ := AlgebraicGeometry.Scheme.Modules.pullbackComp j (AlgebraicGeometry.Scheme.totalSpace V).hom
  have h2 := isZeroAt_map (Θ.inv.app L) _ w h
  have hinv : ((Θ.inv.app L).val.app (Opposite.op ⊤)).hom
      (((Θ.hom.app L).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j τπ)) =
      sectionPullbackAlong j τπ :=
    congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j τπ)) (Θ.hom_inv_id_app L)
  rw [hinv] at h2
  exact isZeroAt_of_isZeroAt_sectionPullbackAlong j _ _ w h2

/-- **Core leaf.** If all coordinates `τ_ℓ = p^*(π_ℓ)(τ)` of the tautological section of
`Tot(A^{⊕(N+1)})` vanish at `v`, then `v` is in the image of the zero section.

Source: Definition 2.1 of the paper (`Z^×` is `Z` minus the zero section; there the
projectivization of `(z_0 : … : z_N)` is defined).

Proof (no affine-local description of `Tot(V)` is needed). Let `ι : Spec κ(v) → Tot(V)` be the
residue-field point of `v` (Mathlib `Scheme.fromSpecResidueField`), `g := ι ≫ p`.
1. `IsZeroAt τ_ℓ v ⇒ ι^*τ_ℓ = 0`: on the one-point scheme `Spec κ(v)` the stalk is a field
   (`stalkClosedPointIso`), so `𝔪 = ⊥` and `IsZeroAt (ι^*τ_ℓ) pt` (transport
   `isZeroAt_sectionPullbackAlong_of_isZeroAt`) means the germ is `0`; a section with zero germ is `0`
   (`section_ext`) — `sectionPullbackAlong_fromSpecResidueField_eq_zero_of_isZeroAt`.
2. All coordinates of `ι^*τ` vanish, hence `ι^*τ = 0` (`sectionPullbackAlong_eq_zero_of_forall_coordinate`:
   transport through `pullbackComp ι p` and use `pullback_biproduct_section_ext`).
3. `ι` is a `T`-point of `Tot(V)` over `g`; its section is `pullbackComp (ι^*τ) = 0`
   (`totalSpaceHomEquiv_naturality`). The section of `g ≫ σ₀` is `0` as well
   (`totalSpaceHomEquiv_eq_zero_of_factors_zeroSection`), so `ι = g ≫ σ₀` by injectivity of
   `totalSpaceHomEquiv`, and `v = ι(pt) = σ₀(g(pt))`
   (`mem_range_zeroSection_of_sectionPullbackAlong_fromSpecResidueField_eq_zero`,
   module `PuncturedConeToProductResidueFieldPoint`).
The same general lemma (`mem_range_zeroSection_of_isZeroAt_tautologicalSection`) also gives the line-bundle
leaf `mem_range_zeroSection_of_isZeroAt_tautological` of `PuncturedTautologicalSectionFrame.lean`. -/
theorem AlgebraicGeometry.Scheme.mem_range_zeroSection_of_forall_isZeroAt_coordinate
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.Modules) [A.IsLineBundle] (N : ℕ)
    (v : (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left)
    (h : ∀ ℓ : Fin (N + 1), IsZeroAt
      ((((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).map
          (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
          (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
          (CategoryTheory.CategoryStruct.id _))) v) :
    v ∈ Set.range (AlgebraicGeometry.Scheme.zeroSection
      (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).base := by
  apply AlgebraicGeometry.Scheme.mem_range_zeroSection_of_sectionPullbackAlong_fromSpecResidueField_eq_zero
  apply sectionPullbackAlong_eq_zero_of_forall_coordinate
    (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom
    (fun _ : Fin (N + 1) => A)
  intro ℓ
  exact sectionPullbackAlong_fromSpecResidueField_eq_zero_of_isZeroAt _ _ v (h ℓ)

end
