import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionInPunctured
import MiyaokaMori.AlgebraicGeometry.Modules.TotLinePunctured

/-! # The tautological section is a frame on the punctured total space

On the punctured total space `P = Tot(V)^×` of a line bundle `V` on `B`, with `π : P → B`, the
tautological section `ξ ∈ Γ(P, π^*V)` is nowhere zero, hence a global frame of the line bundle `π^*V`:
`O_P ≅ π^*V`.

Notation: `π` is written out as `P.ι ≫ (totalSpace V).hom` and the tautological section as
`totalSpaceHomEquiv V (Over.mk π) (Over.homMk P.ι rfl)`; these are, by definition (`rfl`), the
`totalSpacePunctured.toBase V` and `totalSpacePunctured.tautologicalSection V` of
`PuncturedConeIsPuncturedLineBundleContract` (not imported here to keep the import closure small).

Source: the zero section is the closed subscheme of `Tot(V)` where the tautological section vanishes
(Stacks 01CY for "the locus where a section of a line bundle generates is open, and the section is a frame
there"); `P` is by definition the complement of the zero section (`totalSpacePunctured`).
Used for the trivialization of the first term of the tangent sequence (2.2) of the paper
by the Euler section.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- On `Spec K` for a field `K`, the maximal ideal of the stalk at (the only) point is zero: the point is
the closed point, whose stalk is `K` itself (`stalkClosedPointIso`), a field
(`IsLocalRing.isField_iff_maximalIdeal_eq`). Stated for `Spec (CommRingCat.of K)` with `K : Type u`
(as Mathlib's `Unique (Spec (.of K))`), not for `R : CommRingCat` with `[Field R]`, which would create an
instance diamond between `Field.toCommRing` and `R.commRing` inside `PrimeSpectrum`. -/
theorem AlgebraicGeometry.Spec.maximalIdeal_stalk_eq_bot_of_field (K : Type u) [Field K]
    (x : AlgebraicGeometry.Spec (CommRingCat.of K)) :
    IsLocalRing.maximalIdeal ((AlgebraicGeometry.Spec (CommRingCat.of K)).presheaf.stalk x) = ⊥ := by
  rw [← IsLocalRing.isField_iff_maximalIdeal_eq]
  have : IsLocalRing (CommRingCat.of K) := inferInstanceAs (IsLocalRing K)
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  exact MulEquiv.isField (Field.toIsField K)
    (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv

/-- If `𝔪_x = 0` (the stalk `O_{X,x}` is a field), a section that is zero at `x` in the sense of
`IsZeroAt` (germ in `𝔪_x · M_x = 0`) has germ `0` at `x`. -/
theorem IsZeroAt.germ_eq_zero_of_maximalIdeal_eq_bot {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk x) = ⊥) (h : IsZeroAt s x) :
    (M.presheaf.germ ⊤ x trivial).hom s = 0 := by
  have h' : (M.presheaf.germ ⊤ x trivial).hom s ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x)) := h
  rw [hm, Submodule.bot_smul] at h'
  exact (Submodule.mem_bot _).mp h'

/-- On `Spec K` for a field `K` (a one-point scheme whose stalk is `K`), a global section of a sheaf of
modules that is zero at the point (`IsZeroAt`) is zero: its germ at the only point is `0`
(`IsZeroAt.germ_eq_zero_of_maximalIdeal_eq_bot`, `Spec.maximalIdeal_stalk_eq_bot_of_field`), and a
section of a sheaf with all germs zero is zero (`TopCat.Presheaf.section_ext`). -/
theorem IsZeroAt.eq_zero_of_spec_field (K : Type u) [Field K]
    (M : (AlgebraicGeometry.Spec (CommRingCat.of K)).Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u))
    (x : AlgebraicGeometry.Spec (CommRingCat.of K)) (h : IsZeroAt s x) : s = 0 := by
  refine TopCat.Presheaf.section_ext (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab _) ⊤ s 0 ?_
  intro x' hx'
  obtain rfl : x' = x := Subsingleton.elim _ _
  change (M.presheaf.germ ⊤ x' trivial).hom s = (M.presheaf.germ ⊤ x' trivial).hom 0
  rw [map_zero]
  exact IsZeroAt.germ_eq_zero_of_maximalIdeal_eq_bot s x'
    (AlgebraicGeometry.Spec.maximalIdeal_stalk_eq_bot_of_field K x') h

/-- If the tautological section `ξ := totalSpaceHomEquiv V (Tot V) (𝟙)` of `p^*V` on `T = Tot(V)` is
zero at a point `y` (its germ lies in `𝔪_y · (p^*V)_y`), then `y` lies in the image of the zero section.

Source: the zero section `σ : B → Tot(V)` is the `B`-morphism corresponding (`relativeSpecHomEquiv`) to the
augmentation `Sym(V^∨) → O_B` (`zeroSection`, `symAugmentation`); a `B`-morphism `S → Tot(V)` is the same
as a section of the pulled-back bundle on `S` (`totalSpaceHomEquiv`, Stacks 01LX / Hartshorne II Ex. 5.18),
and it factors through the zero section iff that section is `0`
(`totalSpaceHomEquiv_eq_zero_of_factors_zeroSection`).

Proof (pointwise via the residue field; no local coordinates needed). Let `j : Spec κ(y) → T` be the
canonical morphism with image `{y}` (`Scheme.fromSpecResidueField`, `fromSpecResidueField_apply`), put
`q := j ≫ p`, so `j` is a `B`-morphism `Over.mk q ⟶ T`, corresponding under `totalSpaceHomEquiv` to the
section `j^*ξ ∈ Γ(Spec κ(y), q^*V)` (`totalSpaceHomEquiv_naturality` with `m = 𝟙 T`, transported through
`pullbackComp`). Since `ξ` is zero at `y = j(pt)`, `j^*ξ` is zero at `pt`
(`isZeroAt_sectionPullbackAlong_of_isZeroAt`, `isZeroAt_map`). On `Spec κ(y)` the stalk is the field
`κ(y)`, so `𝔪_pt = 0` and "zero at `pt`" means the germ is `0`; the space is a point, so the section is `0`
(`IsZeroAt.eq_zero_of_spec_field`). The `B`-morphism `q ≫ σ` also corresponds to `0`
(`totalSpaceHomEquiv_eq_zero_of_factors_zeroSection`), so by injectivity of `totalSpaceHomEquiv`,
`j = q ≫ σ` as morphisms `Spec κ(y) → T`. Evaluating at `pt`: `y = j(pt) = σ(q(pt))`.

Edge cases: `B = ∅` — no `y`, vacuous; `y` in the image of the zero section — conclusion holds directly. -/
theorem AlgebraicGeometry.Scheme.mem_range_zeroSection_of_isZeroAt_tautological
    {B : AlgebraicGeometry.Scheme.{u}} (V : B.Modules) [V.IsLineBundle]
    (y : (AlgebraicGeometry.Scheme.totalSpace V).left)
    (h : IsZeroAt (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
      (CategoryTheory.CategoryStruct.id _)) y) :
    y ∈ Set.range (AlgebraicGeometry.Scheme.zeroSection V).base := by
  let j : AlgebraicGeometry.Spec ((AlgebraicGeometry.Scheme.totalSpace V).left.residueField y) ⟶
      (AlgebraicGeometry.Scheme.totalSpace V).left :=
    (AlgebraicGeometry.Scheme.totalSpace V).left.fromSpecResidueField y
  let pt : AlgebraicGeometry.Spec ((AlgebraicGeometry.Scheme.totalSpace V).left.residueField y) :=
    IsLocalRing.closedPoint _
  have hpt : j.base pt = y := AlgebraicGeometry.Scheme.fromSpecResidueField_apply y pt
  -- `ξ` is zero at `y = j pt`, hence `j^*ξ` is zero at `pt`
  have h0 : IsZeroAt (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
      (𝟙 (AlgebraicGeometry.Scheme.totalSpace V))) (j.base pt) := by
    rw [hpt]; exact h
  have h1 : IsZeroAt (sectionPullbackAlong j (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V
      (AlgebraicGeometry.Scheme.totalSpace V) (𝟙 (AlgebraicGeometry.Scheme.totalSpace V)))) pt :=
    isZeroAt_sectionPullbackAlong_of_isZeroAt j _ _ pt h0
  have h2 := isZeroAt_map ((AlgebraicGeometry.Scheme.Modules.pullbackComp j
    (AlgebraicGeometry.Scheme.totalSpace V).hom).hom.app V) _ pt h1
  -- naturality: the section corresponding to `j` is (the transport of) `j^*ξ`
  have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality V
    (AlgebraicGeometry.Scheme.totalSpace V) j (𝟙 (AlgebraicGeometry.Scheme.totalSpace V))
  rw [Category.comp_id] at hn
  rw [← hn] at h2
  -- on `Spec κ(y)`, zero at the point means zero
  have h3 : AlgebraicGeometry.Scheme.totalSpaceHomEquiv V
      (CategoryTheory.Over.mk (j ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom))
      (CategoryTheory.Over.homMk j rfl) = 0 :=
    IsZeroAt.eq_zero_of_spec_field _ _ _ pt h2
  -- the morphism `q ≫ σ` also corresponds to `0`
  have h4 : AlgebraicGeometry.Scheme.totalSpaceHomEquiv V
      (CategoryTheory.Over.mk (j ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom))
      (CategoryTheory.Over.homMk ((j ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom) ≫
          AlgebraicGeometry.Scheme.zeroSection V)
        (by rw [Category.assoc, AlgebraicGeometry.Scheme.zeroSection_comp, Category.comp_id]; rfl)) = 0 :=
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv_eq_zero_of_factors_zeroSection V _ _ rfl
  have h5 := (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V
    (CategoryTheory.Over.mk (j ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom))).injective (h3.trans h4.symm)
  have h6 : j = (j ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom) ≫ AlgebraicGeometry.Scheme.zeroSection V :=
    congrArg CategoryTheory.CommaMorphism.left h5
  refine ⟨(j ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom).base pt, ?_⟩
  calc (AlgebraicGeometry.Scheme.zeroSection V).base ((j ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom).base pt)
      = ((j ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom) ≫ AlgebraicGeometry.Scheme.zeroSection V).base pt :=
        rfl
    _ = j.base pt := by rw [← h6]
    _ = y := hpt

/-- The tautological section of `π^*V` on the punctured total space is nowhere zero: its zero locus on
`Tot(V)` is the zero section (`mem_range_zeroSection_of_isZeroAt_tautological`), which `P` avoids by
definition. The tautological section on `P` is the pullback along `P.ι` of the one on `Tot(V)`
(`totalSpaceHomEquiv_naturality`), and pulling back preserves "is zero at"
(`isZeroAt_of_isZeroAt_sectionPullbackAlong`). -/
theorem AlgebraicGeometry.Scheme.totalSpacePunctured.not_isZeroAt_tautologicalSection
    {B : AlgebraicGeometry.Scheme.{u}} (V : B.Modules) [V.IsLineBundle]
    (y : (AlgebraicGeometry.Scheme.totalSpacePunctured V).toScheme) :
    ¬ IsZeroAt (M := (AlgebraicGeometry.Scheme.Modules.pullback
        ((AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫
          (AlgebraicGeometry.Scheme.totalSpace V).hom)).obj V)
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V
        (CategoryTheory.Over.mk ((AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫
          (AlgebraicGeometry.Scheme.totalSpace V).hom))
        (CategoryTheory.Over.homMk (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι rfl)) y := by
  intro hz
  -- the tautological section on `P` is the pullback of `ξ` along `P.ι`
  have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality V
    (AlgebraicGeometry.Scheme.totalSpace V) (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
    (𝟙 (AlgebraicGeometry.Scheme.totalSpace V))
  rw [Category.comp_id] at hn
  have h1 : IsZeroAt ((((AlgebraicGeometry.Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
      (AlgebraicGeometry.Scheme.totalSpace V).hom).hom.app V).val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
          (𝟙 (AlgebraicGeometry.Scheme.totalSpace V))))) y := by
    rw [← hn]; exact hz
  have h2 := isZeroAt_map ((AlgebraicGeometry.Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
      (AlgebraicGeometry.Scheme.totalSpace V).hom).inv.app V) _ y h1
  have hinv := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
          (𝟙 (AlgebraicGeometry.Scheme.totalSpace V)))))
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
      (AlgebraicGeometry.Scheme.totalSpace V).hom).hom_inv_id_app V)
  have h0 : (((AlgebraicGeometry.Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
      (AlgebraicGeometry.Scheme.totalSpace V).hom).inv.app V).val.app (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
        (AlgebraicGeometry.Scheme.totalSpace V).hom).hom.app V).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
            (𝟙 (AlgebraicGeometry.Scheme.totalSpace V))))) =
      sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
          (𝟙 (AlgebraicGeometry.Scheme.totalSpace V))) := hinv
  rw [h0] at h2
  have h3 := isZeroAt_of_isZeroAt_sectionPullbackAlong
    (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι _ _ y h2
  have h4 := AlgebraicGeometry.Scheme.mem_range_zeroSection_of_isZeroAt_tautological V _ h3
  -- but `P.ι.base y ∈ P = (range zeroSection)ᶜ`
  have h5 : (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι.base y ∈
      (AlgebraicGeometry.Scheme.totalSpacePunctured V : Set (AlgebraicGeometry.Scheme.totalSpace V).left) := by
    have hr := AlgebraicGeometry.Scheme.Opens.opensRange_ι (AlgebraicGeometry.Scheme.totalSpacePunctured V)
    have hmem : (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι.base y ∈
        (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι.opensRange := ⟨y, rfl⟩
    rw [hr] at hmem
    exact hmem
  exact h5 h4

/-- Near a point where the global section `s` of a line bundle `M` is not zero (`¬ IsZeroAt s x`), `s` is a
frame: take a frame `e` of `M` on `W ∋ x` and write `s|_W = f • e`; then `s_x = f_x • e_x`, so `f_x ∉ 𝔪_x`,
i.e. `x ∈ X_f`, and on the basic open `X_f` the coordinate `f` is a unit, so `s|_{X_f}` is a frame
(`IsFrame.of_isUnit_coord`). This is the argument of `isOpen_setOf_germ_notMem_maximalIdeal_smul`
(Stacks 01CY) with the frame made explicit. -/
theorem AlgebraicGeometry.Scheme.Modules.IsFrame.exists_of_not_isZeroAt {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsLineBundle] (s : Γ(M, ⊤)) (x : X) (h : ¬ IsZeroAt s x) :
    ∃ W : X.Opens, x ∈ W ∧ AlgebraicGeometry.Scheme.Modules.IsFrame M W (M.res le_top s) := by
  obtain ⟨W, hxW, e, hf⟩ := AlgebraicGeometry.Scheme.Modules.exists_frame M x
  set f : Γ(X, W) := hf.coord le_rfl (M.res le_top s) with hfdef
  have hse : M.res le_top s = f • e := by
    have h1 := hf.coord_smul_frame le_rfl (M.res le_top s)
    rw [AlgebraicGeometry.Scheme.Modules.res_self] at h1
    exact h1.symm
  have key : ∀ (y : X) (hy : y ∈ W),
      M.presheaf.germ ⊤ y trivial s = X.presheaf.germ W y hy f • M.presheaf.germ W y hy e := by
    intro y hy
    have h0 : M.presheaf.germ W y hy (M.res le_top s) = M.presheaf.germ ⊤ y trivial s :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [← h0, hse, AlgebraicGeometry.Scheme.Modules.germ_smul']
  have hx' : x ∈ X.basicOpen f := by
    rw [X.mem_basicOpen f x hxW]
    by_contra hnu
    apply h
    show M.presheaf.germ ⊤ x trivial s ∈ _
    rw [key x hxW]
    exact Submodule.smul_mem_smul (N := (⊤ : Submodule (X.presheaf.stalk x) (M.stalk x)))
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
  have hle : X.basicOpen f ≤ W := X.basicOpen_le f
  refine ⟨X.basicOpen f, hx', ?_⟩
  have hfr : AlgebraicGeometry.Scheme.Modules.IsFrame M (X.basicOpen f) (M.res hle e) := hf.restrict hle
  apply hfr.of_isUnit_coord
  have hc : hfr.coord le_rfl (M.res le_top s) = X.presheaf.map (homOfLE hle).op f := by
    apply hfr.coord_unique
    rw [AlgebraicGeometry.Scheme.Modules.res_self, ← AlgebraicGeometry.Scheme.Modules.res_smul, ← hse]
    exact AlgebraicGeometry.Scheme.Modules.res_res M hle le_top s
  rw [hc]
  exact X.toRingedSpace.isUnit_res_basicOpen f

/-- A global section of a line bundle that is nowhere zero (no germ lies in `𝔪_x M_x`) is a global frame
(Stacks 01CY): it is a frame near every point (`IsFrame.exists_of_not_isZeroAt`) and frames are local
(`IsFrame.of_iSup`). -/
theorem AlgebraicGeometry.Scheme.Modules.IsFrame.of_not_isZeroAt {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsLineBundle] (s : Γ(M, ⊤))
    (h : ∀ x : X, ¬ IsZeroAt s x) :
    AlgebraicGeometry.Scheme.Modules.IsFrame M ⊤ s := by
  choose W hxW hfr using fun x =>
    AlgebraicGeometry.Scheme.Modules.IsFrame.exists_of_not_isZeroAt M s x (h x)
  refine AlgebraicGeometry.Scheme.Modules.IsFrame.of_iSup W (fun _ => le_top) ?_ hfr
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hxW x⟩

/-- The tautological section is a global frame of `π^*V` on `Tot(V)^×` (`π = P.ι ≫ (totalSpace V).hom`). -/
theorem AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection_isFrame
    {B : AlgebraicGeometry.Scheme.{u}} (V : B.Modules) [V.IsLineBundle] :
    AlgebraicGeometry.Scheme.Modules.IsFrame
      ((AlgebraicGeometry.Scheme.Modules.pullback ((AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫
        (AlgebraicGeometry.Scheme.totalSpace V).hom)).obj V)
      ⊤ (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V
        (CategoryTheory.Over.mk ((AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫
          (AlgebraicGeometry.Scheme.totalSpace V).hom))
        (CategoryTheory.Over.homMk (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι rfl)) :=
  AlgebraicGeometry.Scheme.Modules.IsFrame.of_not_isZeroAt
    ((AlgebraicGeometry.Scheme.Modules.pullback ((AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫
        (AlgebraicGeometry.Scheme.totalSpace V).hom)).obj V) _
    (AlgebraicGeometry.Scheme.totalSpacePunctured.not_isZeroAt_tautologicalSection V)

/-- `O_P ≅ π^*V` on the punctured total space, given by the tautological frame. -/
theorem AlgebraicGeometry.Scheme.totalSpacePunctured.unit_iso_pullback
    {B : AlgebraicGeometry.Scheme.{u}} (V : B.Modules) [V.IsLineBundle] :
    Nonempty ((show (AlgebraicGeometry.Scheme.totalSpacePunctured V).toScheme.Modules from
        SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpacePunctured V).toScheme.ringCatSheaf) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback ((AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫
        (AlgebraicGeometry.Scheme.totalSpace V).hom)).obj V) :=
  ⟨(AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection_isFrame V).topTrivialization⟩

end
