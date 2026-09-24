import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionInPunctured
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivNaturality
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivZeroSection

/-! # A point where the tautological section vanishes lies in the zero section

**The zero locus of the tautological section is the zero section** (pointwise, for any locally free
finite-type `V` on `X`): if the tautological section `τ := totalSpaceHomEquiv V (Tot V) (𝟙)` of `p^*V` is
zero at a point `y ∈ Tot(V)` (`IsZeroAt`: its germ lies in `𝔪_y (p^*V)_y`), then `y` lies in the image of
the zero section `σ₀ = zeroSection V`.

Route (no affine-local description of `Tot(V)` is needed): use the residue-field point
`ι : Spec κ(y) → Tot(V)` (Mathlib `Scheme.fromSpecResidueField`).
1. `Spec κ(y)` is a one-point scheme whose stalk is a field (`stalkClosedPointIso`), so its maximal ideal
   is `⊥`; a section whose germ at the point is zero is zero (`TopCat.Presheaf.section_ext`). Hence
   `IsZeroAt s x ⇒ ι^*s = 0` (`sectionPullbackAlong_fromSpecResidueField_eq_zero_of_isZeroAt`), using the
   transport `isZeroAt_sectionPullbackAlong_of_isZeroAt`.
2. `ι` is an `X`-point of `Tot(V)` over `g := ι ≫ p`; by naturality of the section–morphism correspondence
   (`totalSpaceHomEquiv_naturality`) its section is `pullbackComp (ι^*τ) = 0`.
3. The section of `g ≫ σ₀` is also `0` (`totalSpaceHomEquiv_eq_zero_of_factors_zeroSection`), so by
   injectivity of `totalSpaceHomEquiv`, `ι = g ≫ σ₀`; evaluating at the point of `Spec κ(y)`
   (`fromSpecResidueField_apply`) gives `y = σ₀(g(pt))`.
Also: the coordinate version (`sectionPullbackAlong_eq_zero_of_forall_coordinate`): if all coordinates
`g^*(π_ℓ) s` of a section `s` of `g^*(⨁ A)` pull back to `0` along `j`, so does `s`
(`pullback_biproduct_section_ext` on the source of `j`, after transporting through `pullbackComp`).
So "all coordinates of `τ` vanish at `v`" gives `ι^*τ = 0` coordinatewise (step 1), hence `v ∈ σ₀(X)`.

Source: Definition 2.1 of the paper (`Z^× = Z ∖ σ₀(C)` is where the coordinates are not all zero);
Hartshorne, *Algebraic Geometry*, II Ex. 5.18 (total space of a vector bundle).
This also implies `mem_range_zeroSection_of_isZeroAt_tautological` of
`PuncturedTautologicalSectionFrame.lean` (the line-bundle case).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The stalk of `Spec κ(x)` at its unique point is a field (`stalkClosedPointIso`), so its maximal ideal
is `⊥`. -/
theorem AlgebraicGeometry.Scheme.maximalIdeal_stalk_specResidueField_eq_bot
    {X : AlgebraicGeometry.Scheme.{u}} (x : X) (p : AlgebraicGeometry.Spec (X.residueField x)) :
    IsLocalRing.maximalIdeal ((AlgebraicGeometry.Spec (X.residueField x)).presheaf.stalk p) = ⊥ := by
  have hloc : IsLocalRing ((AlgebraicGeometry.Spec (X.residueField x)).presheaf.stalk p) := inferInstance
  have hp : p = IsLocalRing.closedPoint (X.residueField x) := Subsingleton.elim _ _
  subst hp
  have hK : IsField ((AlgebraicGeometry.Spec (X.residueField x)).presheaf.stalk
      (IsLocalRing.closedPoint (X.residueField x))) :=
    MulEquiv.isField (Field.toIsField (X.residueField x))
      (AlgebraicGeometry.stalkClosedPointIso (X.residueField x)).commRingCatIsoToRingEquiv.toMulEquiv
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mp hK

/-- A global section that is zero at `x` pulls back to `0` on the residue-field point `Spec κ(x) → X`:
on the one-point scheme `Spec κ(x)` the germ determines the section (`section_ext`) and the maximal ideal
of the stalk is `⊥`. -/
theorem sectionPullbackAlong_fromSpecResidueField_eq_zero_of_isZeroAt {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X) (h : IsZeroAt s x) :
    sectionPullbackAlong (X.fromSpecResidueField x) s = 0 := by
  refine TopCat.Presheaf.section_ext
    (⟨((AlgebraicGeometry.Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M).presheaf,
      ((AlgebraicGeometry.Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M).isSheaf⟩ :
      TopCat.Sheaf Ab (AlgebraicGeometry.Spec (X.residueField x))) ⊤ _ 0 ?_
  intro y hy
  have h' : IsZeroAt s ((X.fromSpecResidueField x).base y) := by
    rw [show (X.fromSpecResidueField x).base y = x from
      AlgebraicGeometry.Scheme.fromSpecResidueField_apply x y]
    exact h
  have hz : IsZeroAt (sectionPullbackAlong (X.fromSpecResidueField x) s) y :=
    isZeroAt_sectionPullbackAlong_of_isZeroAt (X.fromSpecResidueField x) M s y h'
  have hmem : (((AlgebraicGeometry.Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M).presheaf.germ
      ⊤ y trivial).hom (sectionPullbackAlong (X.fromSpecResidueField x) s) ∈
      (IsLocalRing.maximalIdeal ((AlgebraicGeometry.Spec (X.residueField x)).presheaf.stalk y)) •
        (⊤ : Submodule ((AlgebraicGeometry.Spec (X.residueField x)).presheaf.stalk y)
          (((AlgebraicGeometry.Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M).presheaf.stalk y)) :=
    hz
  rw [AlgebraicGeometry.Scheme.maximalIdeal_stalk_specResidueField_eq_bot, Submodule.bot_smul,
    Submodule.mem_bot] at hmem
  change (((AlgebraicGeometry.Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M).presheaf.germ
      ⊤ y hy).hom (sectionPullbackAlong (X.fromSpecResidueField x) s) =
    (((AlgebraicGeometry.Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M).presheaf.germ
      ⊤ y hy).hom 0
  rw [map_zero]
  exact hmem

/-- **Core**: if the tautological section `τ` pulls back to `0` on the residue-field point
`ι : Spec κ(y) → Tot(V)`, then `y` lies on the zero section. Steps 2–3 of the module docstring. -/
theorem AlgebraicGeometry.Scheme.mem_range_zeroSection_of_sectionPullbackAlong_fromSpecResidueField_eq_zero
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (y : (AlgebraicGeometry.Scheme.totalSpace V).left)
    (h0 : sectionPullbackAlong ((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y)
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
        (CategoryTheory.CategoryStruct.id _)) = 0) :
    y ∈ Set.range (AlgebraicGeometry.Scheme.zeroSection V).base := by
  have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality V (AlgebraicGeometry.Scheme.totalSpace V)
    ((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y)
    (𝟙 (AlgebraicGeometry.Scheme.totalSpace V))
  rw [Category.comp_id, h0, map_zero] at hn
  have hw : (((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y ≫
        (AlgebraicGeometry.Scheme.totalSpace V).hom) ≫ AlgebraicGeometry.Scheme.zeroSection V) ≫
        (AlgebraicGeometry.Scheme.totalSpace V).hom =
      (AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y ≫
        (AlgebraicGeometry.Scheme.totalSpace V).hom := by
    rw [Category.assoc, AlgebraicGeometry.Scheme.zeroSection_comp, Category.comp_id]
  have hz := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_eq_zero_of_factors_zeroSection V
    (CategoryTheory.Over.mk ((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y ≫
      (AlgebraicGeometry.Scheme.totalSpace V).hom))
    (CategoryTheory.Over.homMk (((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y ≫
      (AlgebraicGeometry.Scheme.totalSpace V).hom) ≫ AlgebraicGeometry.Scheme.zeroSection V) hw) rfl
  have heq := (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V
    (CategoryTheory.Over.mk ((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y ≫
      (AlgebraicGeometry.Scheme.totalSpace V).hom))).injective (hn.trans hz.symm)
  have hιeq : (AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y =
      ((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y ≫
        (AlgebraicGeometry.Scheme.totalSpace V).hom) ≫ AlgebraicGeometry.Scheme.zeroSection V :=
    congrArg CategoryTheory.CommaMorphism.left heq
  refine ⟨((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y ≫
    (AlgebraicGeometry.Scheme.totalSpace V).hom).base default, ?_⟩
  have h1 : ((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y).base default = y :=
    AlgebraicGeometry.Scheme.fromSpecResidueField_apply y default
  calc (AlgebraicGeometry.Scheme.zeroSection V).base
        (((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y ≫
          (AlgebraicGeometry.Scheme.totalSpace V).hom).base default)
      = (((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y ≫
          (AlgebraicGeometry.Scheme.totalSpace V).hom) ≫ AlgebraicGeometry.Scheme.zeroSection V).base default :=
        (AlgebraicGeometry.Scheme.Hom.comp_apply _ _ _).symm
    _ = ((AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y).base default := by
        rw [← hιeq]
    _ = y := h1

/-- **A point where the tautological section vanishes lies on the zero section** (any locally free
finite-type `V`): combine step 1 with the core. -/
theorem AlgebraicGeometry.Scheme.mem_range_zeroSection_of_isZeroAt_tautologicalSection
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (y : (AlgebraicGeometry.Scheme.totalSpace V).left)
    (h : IsZeroAt (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
      (CategoryTheory.CategoryStruct.id _)) y) :
    y ∈ Set.range (AlgebraicGeometry.Scheme.zeroSection V).base :=
  AlgebraicGeometry.Scheme.mem_range_zeroSection_of_sectionPullbackAlong_fromSpecResidueField_eq_zero V y
    (sectionPullbackAlong_fromSpecResidueField_eq_zero_of_isZeroAt _ _ y h)

/-- If every coordinate `g^*(π_ℓ) s` of a section `s` of `g^*(⨁ A)` pulls back to `0` along `j : S → T`,
then `s` pulls back to `0`: transport `j^*s` through `pullbackComp j g` to a section of `(j ≫ g)^*(⨁ A)`
whose coordinates are the transported `j^*(g^*(π_ℓ) s) = 0` (`sectionPullbackAlong_naturality`, naturality of
`pullbackComp`), and use `pullback_biproduct_section_ext`. -/
theorem sectionPullbackAlong_eq_zero_of_forall_coordinate {X T S : AlgebraicGeometry.Scheme.{u}}
    (g : T ⟶ X) {n : ℕ} (A : Fin n → X.Modules) (j : S ⟶ T)
    (s : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj (⨁ A)).val.obj (Opposite.op ⊤) : Type u))
    (h : ∀ ℓ, sectionPullbackAlong j ((((AlgebraicGeometry.Scheme.Modules.pullback g).map
      (biproduct.π A ℓ)).val.app (Opposite.op ⊤)).hom s) = 0) :
    sectionPullbackAlong j s = 0 := by
  have hΦ : (((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app (⨁ A)).val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong j s) = 0 := by
    apply AlgebraicGeometry.Scheme.Modules.pullback_biproduct_section_ext (j ≫ g) A
    intro ℓ
    rw [map_zero]
    have hnat := (AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.naturality (biproduct.π A ℓ)
    have h1 := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j s)) hnat
    refine (h1.symm.trans ?_)
    show (((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app (A ℓ)).val.app (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullback j).map ((AlgebraicGeometry.Scheme.Modules.pullback g).map
        (biproduct.π A ℓ))).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j s)) = 0
    rw [← sectionPullbackAlong_naturality, h ℓ, map_zero]
  have hinv := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j s))
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom_inv_id_app (⨁ A))
  have h0 : (((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).inv.app (⨁ A)).val.app (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app (⨁ A)).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong j s)) = sectionPullbackAlong j s := hinv
  rw [← h0, hΦ, map_zero]

end
