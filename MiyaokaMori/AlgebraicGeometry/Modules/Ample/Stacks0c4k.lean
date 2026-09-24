import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.IsAmpleOfIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0892
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0c4k_IsAmplePullbackIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0c4k_RelativelyAmpleLocal

/-! # Relative ampleness along a composition (Stacks 0C4K)

Stacks 0C4K: if `S` is quasi-compact, `M` is `g`-ample and `L` is `f`-ample (`f`, `g`
quasi-compact), then `L ⊗ f^*M^{⊗a}` is `g∘f`-ample for `a ≫ 0`.

Reference: Stacks 0C4K (`morphisms-lemma-ample-composition`).

Proof sketch:
1. `S` quasi-compact ⇒ a finite affine open cover `𝒲` (`isCompact_iff_finite_and_eq_biUnion_affineOpens`).
2. For each affine open `i`, put `Y_i := g⁻¹ i`, `X_i := f⁻¹ Y_i`, `f_i := f ∣_ Y_i`. `L|_{X_i}` is
   relatively ample for `f_i` (`isAmple_pullback_preimage_morphismRestrict`: the image of an affine
   open `V` of `Y_i` along `Y_i.ι` is an affine open `V'` of `Y`, and `f_i⁻¹V`, `f⁻¹V'` are the same
   open subscheme of `X`; transport with `IsAmple.pullback_of_isIso`), `M|_{Y_i}` is ample (`hM`),
   so Stacks 0892(1) gives `a_i`.
3. `a₀ := max_{i ∈ 𝒲} a_i`. For `a ≥ a₀` and `i ∈ 𝒲`:
   `(L ⊗ f^*M^{⊗a})|_{X_i} ≅ L|_{X_i} ⊗ f_i^*(M|_{Y_i})^{⊗a}` (`restrictTensorPullbackIso`: pullback
   commutes with tensor products, tensor powers and composition), hence ample.
4. Relative ampleness is local on the base (Stacks 01VJ (1)⇒(3),
   `isAmple_pullback_preimage_of_isAmple_on_affine_cover`): `f ≫ g` is quasi-compact and `𝒲` covers
   `S`, so `(L ⊗ f^*M^{⊗a})|_{(f≫g)⁻¹W}` is ample for every affine open `W`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Relative ampleness restricts to open subschemes of the base: if `L` is relatively ample for `f`
(ample on the preimage of every affine open), then for an open `U` of `Y`, `L|_{f⁻¹U}` is relatively
ample for `f ∣_ U : f⁻¹U ⟶ U`.
Proof: the image `V' := U.ι ''ᵁ V` of an affine open `V` of `U` is an affine open of `Y`
(`IsAffineOpen.image_of_isOpenImmersion`); `(f ∣_ U)⁻¹V ↪ f⁻¹U ↪ X` and `f⁻¹V' ↪ X` are open
immersions with the same image (`image_morphismRestrict_preimage`), so `IsOpenImmersion.isoOfRangeEq`
gives an isomorphism `e` with `e ≫ (f⁻¹V').ι = j₁`; transport `hL V'` with `pullbackComp` and
`IsAmple.pullback_of_isIso`. -/
theorem AlgebraicGeometry.isAmple_pullback_preimage_morphismRestrict
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (L : X.Modules) [L.IsLineBundle]
    (hL : ∀ V : Y.affineOpens,
      AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj L))
    (U : Y.Opens) (V : (U : AlgebraicGeometry.Scheme.{u}).affineOpens) :
    AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback ((f ∣_ U) ⁻¹ᵁ V.1).ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L)) := by
  have hV' : AlgebraicGeometry.IsAffineOpen (U.ι ''ᵁ V.1) := V.2.image_of_isOpenImmersion U.ι
  have hrange : Set.range (((f ∣_ U) ⁻¹ᵁ V.1).ι ≫ (f ⁻¹ᵁ U).ι) =
      Set.range (f ⁻¹ᵁ (U.ι ''ᵁ V.1)).ι := by
    have h : (((f ∣_ U) ⁻¹ᵁ V.1).ι ≫ (f ⁻¹ᵁ U).ι).opensRange = (f ⁻¹ᵁ (U.ι ''ᵁ V.1)).ι.opensRange := by
      rw [AlgebraicGeometry.Scheme.Hom.opensRange_comp, AlgebraicGeometry.Scheme.Opens.opensRange_ι,
        AlgebraicGeometry.Scheme.Opens.opensRange_ι]
      exact AlgebraicGeometry.image_morphismRestrict_preimage f U V.1
    exact congrArg (fun W : X.Opens => (W : Set X)) h
  let e := AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq _ _ hrange
  have hfac : e.hom ≫ (f ⁻¹ᵁ (U.ι ''ᵁ V.1)).ι = ((f ∣_ U) ⁻¹ᵁ V.1).ι ≫ (f ⁻¹ᵁ U).ι :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  have h1 : AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ (U.ι ''ᵁ V.1)).ι).obj L)) :=
    AlgebraicGeometry.IsAmple.pullback_of_isIso e.hom _ (hL ⟨_, hV'⟩)
  have h2 : AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback
      (((f ∣_ U) ⁻¹ᵁ V.1).ι ≫ (f ⁻¹ᵁ U).ι)).obj L) := by
    refine AlgebraicGeometry.IsAmple.of_iso ?_ h1
    exact (AlgebraicGeometry.Scheme.Modules.pullbackComp e.hom _).app L ≪≫
      CategoryTheory.eqToIso (by rw [hfac])
  refine AlgebraicGeometry.IsAmple.of_iso ?_ h2
  exact ((AlgebraicGeometry.Scheme.Modules.pullbackComp _ _).app L).symm

/-- `(L ⊗ f^*P)|_{f⁻¹U} ≅ L|_{f⁻¹U} ⊗ (f ∣_ U)^*(P|_U)`, and for `P = M^{⊗a}` pullback commutes with
tensor powers: `(L ⊗ f^*M^{⊗a})|_{f⁻¹U} ≅ L|_{f⁻¹U} ⊗ (f ∣_ U)^*((M|_U)^{⊗a})`.
Built from `pullbackTensorIso` (pullback commutes with tensor products, Stacks 01CD), `pullbackComp`
(pseudofunctoriality of pullback), `morphismRestrict_ι` (`f ∣_ U ≫ U.ι = (f⁻¹U).ι ≫ f`) and
`pullbackTensorPowIso`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.restrictTensorPullbackTensorPowIso
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (L : X.Modules) (M : Y.Modules) (a : ℕ)
    (U : Y.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj
        (AlgebraicGeometry.Scheme.Modules.tensor L
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow M a))) ≅
      AlgebraicGeometry.Scheme.Modules.tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L)
        ((AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow
            ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M) a)) :=
  AlgebraicGeometry.Scheme.Modules.pullbackTensorIso (f ⁻¹ᵁ U).ι L _ ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
    CategoryTheory.MonoidalCategory.whiskerLeftIso
      ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L)
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app
          (AlgebraicGeometry.Scheme.Modules.tensorPow M a) ≪≫
        CategoryTheory.eqToIso (by rw [AlgebraicGeometry.morphismRestrict_ι]) ≪≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app
          (AlgebraicGeometry.Scheme.Modules.tensorPow M a)).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).mapIso
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso U.ι M a)) ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm

/- Stacks 0C4K: relative ampleness along a composition. Relative ampleness is written as in
   Stacks 01VJ(3), "ample on the preimage of every affine open of the target" (the same form as
   `IsQuasiProjectiveMorphism.exists_relativelyAmple`). -/

theorem AlgebraicGeometry.exists_relativelyAmple_tensor_pullback_tensorPow_comp
    {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [CompactSpace S]
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiCompact g]
    (L : X.Modules) [L.IsLineBundle] (M : Y.Modules) [M.IsLineBundle]
    (hL : ∀ V : Y.affineOpens,
      AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj L))
    (hM : ∀ W : S.affineOpens,
      AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback (g ⁻¹ᵁ W.1).ι).obj M)) :
    ∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ W : S.affineOpens,
      AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback ((f ≫ g) ⁻¹ᵁ W.1).ι).obj
        (AlgebraicGeometry.Scheme.Modules.tensor L
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow M a)))) := by
  -- 1. a finite affine open cover
  have hS : IsCompact ((⊤ : S.Opens) : Set S) := by
    rw [TopologicalSpace.Opens.coe_top]
    exact isCompact_univ
  obtain ⟨𝒲, hfin, hcov⟩ := AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hS
  -- 2. Stacks 0892(1) on each piece
  have key : ∀ i : S.affineOpens, ∃ a₀ : ℕ, ∀ a ≥ a₀,
      AlgebraicGeometry.IsAmple (AlgebraicGeometry.Scheme.Modules.tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ (g ⁻¹ᵁ i.1)).ι).obj L)
        ((AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ (g ⁻¹ᵁ i.1))).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow
            ((AlgebraicGeometry.Scheme.Modules.pullback (g ⁻¹ᵁ i.1).ι).obj M) a))) := fun i =>
    AlgebraicGeometry.exists_isAmple_tensor_pullback_tensorPow (f ∣_ (g ⁻¹ᵁ i.1)) _ _
      (AlgebraicGeometry.isAmple_pullback_preimage_morphismRestrict f L hL (g ⁻¹ᵁ i.1)) (hM i)
  choose a ha using key
  -- 3. a₀ := max; 4. relative ampleness is local on the base
  refine ⟨hfin.toFinset.sup a, fun b hb W => ?_⟩
  refine AlgebraicGeometry.isAmple_pullback_preimage_of_isAmple_on_affine_cover (f ≫ g) _ 𝒲 hcov
    (fun i hi => ?_) W
  have hbi : a i ≤ b := le_trans (Finset.le_sup (f := a) (hfin.mem_toFinset.mpr hi)) hb
  -- instance search does not find the two IsLineBundle instances below in this context (it does in
  -- the statement), so they are constructed explicitly (IsLineBundle is a Prop)
  have hin : (AlgebraicGeometry.Scheme.Modules.tensor L
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow M b))).IsLineBundle :=
    isLineBundle_tensor_pullback_tensorPow f L M b
  have hL' : ((AlgebraicGeometry.Scheme.Modules.pullback ((f ≫ g) ⁻¹ᵁ i.1).ι).obj
      (AlgebraicGeometry.Scheme.Modules.tensor L
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow M b)))).IsLineBundle :=
    SheafOfModules.IsLineBundle.pullback _ _
  exact @AlgebraicGeometry.IsAmple.of_iso _ _ _
    (isLineBundle_tensor_pullback_tensorPow (f ∣_ (g ⁻¹ᵁ i.1))
      ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ (g ⁻¹ᵁ i.1)).ι).obj L)
      ((AlgebraicGeometry.Scheme.Modules.pullback (g ⁻¹ᵁ i.1).ι).obj M) b) hL'
    (AlgebraicGeometry.Scheme.Modules.restrictTensorPullbackTensorPowIso f L M b (g ⁻¹ᵁ i.1)).symm
    (ha i b hbi)

end
