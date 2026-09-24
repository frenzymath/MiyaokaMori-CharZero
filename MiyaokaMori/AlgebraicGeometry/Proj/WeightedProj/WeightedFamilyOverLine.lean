import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Morphisms.FamilyProjectiveOverLineGeneral
import MiyaokaMori.AlgebraicGeometry.Morphisms.LocallyProductFlat
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Modules.RestrictToLambda
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01o3

/-! # The weighted family over the affine line

Let `X` be a projective scheme over a field `k` and `S` a graded quasi-coherent algebra on
`X × A¹` which is locally the weighted polynomial algebra of weights `w` (`1 ≤ w_i ≤ κ`, nonempty
finite variable set `σ`). Put `𝒴 = Proj_{X×A¹} S` and `f : 𝒴 → X × A¹ → A¹_k`. Then
(a) `f` is flat; (b) `f` is projective; (c) for every `t ∈ k`, the fiber of `f` over the
`k`-rational point `λ = t` is isomorphic over `X` to `Proj_X (S|_{λ=t})` (where `S|_{λ=t}` is the
pullback along the section `sectionAt t`), and for every `d` the restriction of `O_𝒴(d)` to the
fiber corresponds to `O_{Proj S|_{λ=t}}(d)`.

This is the general form of the "projective flat family" argument in the proof of the reduction to
a split weighted bundle in the paper.

Proof:
1. (a) `relativeProj_locallyWeighted_localProduct` gives an open cover of `X × A¹` over which `𝒴`
   is a product with `P_k(w)`; `P_k(w) → Spec k` is flat, so `flat_of_locally_product` makes
   `𝒴 → X × A¹` flat; `toLine : X × A¹ → A¹_k` is the base change of the flat morphism `X → Spec k`
   (`AffineSpace.isPullback_map`), hence flat; the composite is flat.
2. (b) `relativeProj_locallyWeighted_isProjective_over_line`: for `m = |σ| · w_κ` the Veronese
   `S^{(m)}` is generated in degree one and `S^{(m)}_1 = S_m` is of finite type, and
   `𝒴 ≅ Proj S^{(m)}`, so `𝒴 → X × A¹` is projective; `X → Spec k` is projective, its base change
   `X × A¹ → A¹_k` is projective; `A¹_k` is affine, so the composite is projective.
3. (c) `point k t` is a `k`-rational point of `A¹_k`: `sectionAt (Spec k) t : Spec k → A¹_k`
   factors through Mathlib's `SpecToEquivOfField` as `Spec φ ≫ fromSpecResidueField (point k t)`,
   where `φ : κ(point k t) → k` is a homomorphism of fields (hence mono) with a section given by
   `sectionAt ≫ (A¹_k ↘ Spec k) = 𝟙` (hence split epi), so `φ` is an isomorphism
   (`isIso_of_mono_of_isSplitEpi`). The square `X →(sectionAt t) X × A¹ →(toLine) A¹_k` /
   `X → Spec k →(sectionAt t) A¹_k` is a pullback (`AffineSpace.isPullback_map` and
   `IsPullback.of_right`), and the isomorphism `Spec φ` replaces the bottom edge by
   `fromSpecResidueField (point k t)`. Then
   `f.fiber (point k t) = 𝒴 ×_{A¹_k} Spec κ ≅ 𝒴 ×_{X×A¹} X` (`IsPullback.paste_vert`)
   `≅ Proj_X (S.pullback (sectionAt t))` (`relativeProj_baseChange`, Stacks 01O3), compatibly with
   the projection to `X`; the correspondence of `O(d)` is the second part of 01O3, rewritten with
   `Scheme.Modules.pullbackComp`.

References: Stacks 01O3, 02V6, 0C4P.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.affineLineOver

variable {k : Type u} [Field k] (X : AlgebraicGeometry.Scheme.{u})
  [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- `sectionAt t` is a section of `toBase` (`AffineSpace.homOfVector_over`). -/
theorem sectionAt_comp_toBase (t : k) :
    sectionAt X t ≫ toBase X = 𝟙 X :=
  AlgebraicGeometry.AffineSpace.homOfVector_over _ _

/-- `toLine` lies over `X → Spec k` (`AffineSpace.map_over`). -/
theorem toLine_comp_toBase :
    toLine (k := k) X ≫ toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      toBase X ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  AlgebraicGeometry.AffineSpace.map_over _

/-- `toLine` preserves the coordinate function (`AffineSpace.map_appTop_coord`). -/
theorem toLine_appTop_coord (i : ULift.{u} (Fin 1)) :
    (toLine (k := k) X).appTop
        (AlgebraicGeometry.AffineSpace.coord (AlgebraicGeometry.Spec (CommRingCat.of k)) i) =
      AlgebraicGeometry.AffineSpace.coord X i :=
  AlgebraicGeometry.AffineSpace.map_appTop_coord _ _

/-- The coordinate function pulled back along `sectionAt t` is the constant `t`
(`AffineSpace.homOfVector_appTop_coord`). -/
theorem sectionAt_appTop_coord (t : k) (i : ULift.{u} (Fin 1)) :
    (sectionAt X t).appTop (AlgebraicGeometry.AffineSpace.coord X i) =
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv t) :=
  AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord _ _ _

variable (k) in
/-- The section `λ = t` of `A¹_k = Spec k × A¹`, for the trivial structure `⟨𝟙⟩` of `Spec k` over
itself — exactly the morphism whose image of the closed point is `point k t` (see `point`). It is
spelled out because instance search would otherwise pick Mathlib's `specOverSpec`
(`(Spec A).Over (Spec R)` for `[Algebra R A]`, hom `Spec.map (algebraMap R A)`), which is not
definitionally `⟨𝟙 _⟩`. -/
def sectionAtSpec (t : k) :
    AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  letI : (AlgebraicGeometry.Spec (CommRingCat.of k)).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.CategoryStruct.id _⟩
  sectionAt (AlgebraicGeometry.Spec (CommRingCat.of k)) t

variable (k) in
theorem sectionAtSpec_comp_toBase (t : k) :
    sectionAtSpec k t ≫ toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) = 𝟙 _ :=
  AlgebraicGeometry.AffineSpace.homOfVector_over _ _

variable (k) in
theorem sectionAtSpec_appTop_coord (t : k) (i : ULift.{u} (Fin 1)) :
    (sectionAtSpec k t).appTop
        (AlgebraicGeometry.AffineSpace.coord (AlgebraicGeometry.Spec (CommRingCat.of k)) i) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv t :=
  AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord _ _ _

/-- The section `λ = t` of `X × A¹` lies over the section `λ = t` of `A¹_k`. -/
theorem sectionAt_comp_toLine (t : k) :
    sectionAt X t ≫ toLine (k := k) X =
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ sectionAtSpec k t := by
  -- spell everything out in `𝔸(ULift (Fin 1); _)` so that `rw` sees through `affineLineOver`
  change (AlgebraicGeometry.AffineSpace.homOfVector (𝟙 X)
      (fun _ => (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv t)) ≫
      AlgebraicGeometry.AffineSpace.map (ULift.{u} (Fin 1))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :
      X ⟶ AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) (AlgebraicGeometry.Spec (CommRingCat.of k))) =
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
      AlgebraicGeometry.AffineSpace.homOfVector (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k)))
        (fun _ => (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k)) :).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv t))
  ext1
  · rw [Category.assoc, AlgebraicGeometry.AffineSpace.map_over, ← Category.assoc,
      AlgebraicGeometry.AffineSpace.homOfVector_over, Category.id_comp, Category.assoc,
      AlgebraicGeometry.AffineSpace.homOfVector_over, Category.comp_id]
  · rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, CommRingCat.comp_apply, AlgebraicGeometry.AffineSpace.map_appTop_coord,
      AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord,
      AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord, AlgebraicGeometry.Scheme.Hom.id_appTop,
      CommRingCat.id_apply]

/-- The square `X → X × A¹ → A¹_k` / `X → Spec k → A¹_k` (sections `λ = t`) is a pullback. -/
theorem isPullback_sectionAt (t : k) :
    IsPullback (sectionAt X t) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (toLine (k := k) X) (sectionAtSpec k t) := by
  refine IsPullback.of_right (h₁₂ := toBase X)
    (h₂₂ := toBase (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (v₁₃ := X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ?_
    (sectionAt_comp_toLine X t) ?_
  · rw [sectionAt_comp_toBase, sectionAtSpec_comp_toBase]
    exact IsPullback.id_horiz _
  · exact (AlgebraicGeometry.AffineSpace.isPullback_map (n := ULift.{u} (Fin 1))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).flip

variable (k) in
/-- `point k t` is the image of the closed point of `Spec k` under `sectionAtSpec k t`. -/
theorem point_eq (t : k) :
    point k t = (sectionAtSpec k t).base (IsLocalRing.closedPoint k) := by
  have h : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) = IsLocalRing.closedPoint k :=
    Subsingleton.elim _ _
  exact congrArg (fun p => (sectionAtSpec k t).base p) h

/-- `point k t` is a `k`-rational point: `sectionAt (Spec k) t` factors as `Spec φ ≫
fromSpecResidueField (point k t)` with `φ : κ(point k t) ⟶ k` an isomorphism. -/
theorem exists_iso_residueField_point (t : k) :
    ∃ φ : (affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).residueField (point k t) ⟶
        CommRingCat.of k, IsIso φ ∧
      sectionAtSpec k t =
        Spec.map φ ≫ (affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).fromSpecResidueField
          (point k t) := by
  set L := affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) with hL
  set s := sectionAtSpec k t with hs
  have hpt := point_eq k t
  rw [hpt]
  refine ⟨AlgebraicGeometry.Scheme.descResidueField (AlgebraicGeometry.Scheme.stalkClosedPointTo s), ?_, ?_⟩
  · set φ := AlgebraicGeometry.Scheme.descResidueField (AlgebraicGeometry.Scheme.stalkClosedPointTo s)
    have hfac : Spec.map φ ≫ L.fromSpecResidueField (s.base (IsLocalRing.closedPoint k)) = s :=
      AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k L s
    -- mono: a ring hom out of a field is injective
    have : Mono φ := ConcreteCategory.mono_of_injective φ (RingHom.injective φ.hom)
    -- split epi: `s ≫ (L ↘ Spec k) = 𝟙`
    have : IsSplitEpi φ := by
      refine ⟨⟨⟨Spec.preimage (L.fromSpecResidueField (s.base (IsLocalRing.closedPoint k)) ≫
        toBase (AlgebraicGeometry.Spec (CommRingCat.of k))), ?_⟩⟩⟩
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, ← Category.assoc, hfac]
      exact sectionAtSpec_comp_toBase k t
    exact isIso_of_mono_of_isSplitEpi φ
  · exact (AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k L s).symm

/-- The square `X → X × A¹ → A¹_k` / `X → Spec κ(point k t) → A¹_k` is a pullback, for the
isomorphism `φ : κ(point k t) ≅ k` produced by `exists_iso_residueField_point`. -/
theorem isPullback_sectionAt_fromSpecResidueField (t : k)
    (φ : (affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).residueField (point k t) ⟶
        CommRingCat.of k) [IsIso φ]
    (hφ : sectionAtSpec k t =
        Spec.map φ ≫ (affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).fromSpecResidueField
          (point k t)) :
    IsPullback (sectionAt X t) ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ Spec.map φ)
      (toLine (k := k) X)
      ((affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).fromSpecResidueField (point k t)) := by
  have hQ := (isPullback_sectionAt X t).flip
  have hT : IsPullback (Spec.map φ)
      (sectionAtSpec k t)
      ((affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).fromSpecResidueField (point k t))
      (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hφ]⟩
  have := (hQ.paste_horiz hT).flip
  rwa [Category.comp_id] at this

end AlgebraicGeometry.Scheme.affineLineOver

/-- The family `Proj_{X×A¹} S → A¹_k` of a locally weighted polynomial algebra is flat and
projective, and its fiber over the rational point `λ = t` is `Proj_X (S|_{λ=t})` with the
corresponding twisting sheaves. -/
theorem relativeProj_family_over_line {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProjectiveOver k X)
    (S : (AlgebraicGeometry.Scheme.affineLineOver X).GradedQCAlgebra)
    {σ : Type u} [Fintype σ] [Nonempty σ] {κ : ℕ} (w : σ → ℕ) (hw : ∀ i, w i ∈ Finset.Icc 1 κ)
    (hS : S.IsLocallyWeightedPolynomial w (fun i => (Finset.mem_Icc.mp (hw i)).1)) :
    AlgebraicGeometry.Flat ((AlgebraicGeometry.Scheme.relativeProj S).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X) ∧
      AlgebraicGeometry.IsProjectiveMorphism ((AlgebraicGeometry.Scheme.relativeProj S).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X) ∧
      ∀ t : k, ∃ e : ((AlgebraicGeometry.Scheme.relativeProj S).hom ≫
            AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).fiber
              (AlgebraicGeometry.Scheme.affineLineOver.point k t) ≅
          (AlgebraicGeometry.Scheme.relativeProj (S.restrictToLambda t)).left,
        e.hom ≫ (AlgebraicGeometry.Scheme.relativeProj (S.restrictToLambda t)).hom =
          ((AlgebraicGeometry.Scheme.relativeProj S).hom ≫
            AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).fiberι
              (AlgebraicGeometry.Scheme.affineLineOver.point k t) ≫
            (AlgebraicGeometry.Scheme.relativeProj S).hom ≫
            AlgebraicGeometry.Scheme.affineLineOver.toBase X ∧
        ∀ d : ℤ, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
            (((AlgebraicGeometry.Scheme.relativeProj S).hom ≫
              AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).fiberι
                (AlgebraicGeometry.Scheme.affineLineOver.point k t))).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist S d) ≅
          (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist (S.restrictToLambda t) d)) := by
  refine ⟨?_, relativeProj_locallyWeighted_isProjective_over_line hX S w hw hS, ?_⟩
  · -- (a) flatness
    have h1 : AlgebraicGeometry.Flat (AlgebraicGeometry.Scheme.relativeProj S).hom := by
      obtain ⟨𝒰, h𝒰⟩ := relativeProj_locallyWeighted_localProduct.{u, u}
        (AlgebraicGeometry.Scheme.affineLineOver.toBase X ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
        S w (fun i => (Finset.mem_Icc.mp (hw i)).1) hS
      refine flat_of_locally_product (AlgebraicGeometry.Scheme.relativeProj S).hom
        (AlgebraicGeometry.Scheme.affineLineOver.toBase X ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
        (weightedProjectiveSpace k w (fun i => (Finset.mem_Icc.mp (hw i)).1) ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)) 𝒰 fun i => ?_
      obtain ⟨φ, hφ, -⟩ := h𝒰 i
      exact ⟨φ, hφ⟩
    have h2 : AlgebraicGeometry.Flat (AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X) :=
      AlgebraicGeometry.Flat.isStableUnderBaseChange.of_isPullback
        (AlgebraicGeometry.AffineSpace.isPullback_map (n := ULift.{u} (Fin 1))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).flip inferInstance
    exact AlgebraicGeometry.Flat.comp _ _
  · -- (c) fibers at the rational points `λ = t`
    intro t
    obtain ⟨φ, hiso, hφ⟩ :=
      AlgebraicGeometry.Scheme.affineLineOver.exists_iso_residueField_point (k := k) t
    have hB := AlgebraicGeometry.Scheme.affineLineOver.isPullback_sectionAt_fromSpecResidueField
      X t φ hφ
    set P := AlgebraicGeometry.Scheme.relativeProj S with hP
    set sX := AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t with hsX
    have hA := (IsPullback.of_hasPullback sX P.hom).flip
    have hW := hA.paste_vert hB
    obtain ⟨e₀, he₀, htw⟩ := AlgebraicGeometry.Scheme.relativeProj_baseChange sX S
    have he₀' : e₀.inv ≫ (AlgebraicGeometry.Scheme.relativeProj (S.pullback sX)).hom =
        pullback.fst sX P.hom := by
      rw [Iso.inv_comp_eq, he₀]
    have hfst : pullback.fst sX P.hom =
        pullback.snd sX P.hom ≫ P.hom ≫ AlgebraicGeometry.Scheme.affineLineOver.toBase X := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc,
        AlgebraicGeometry.Scheme.affineLineOver.sectionAt_comp_toBase, Category.comp_id]
    refine ⟨hW.isoPullback.symm ≪≫ e₀.symm, ?_, ?_⟩
    · show (hW.isoPullback.inv ≫ e₀.inv) ≫ (AlgebraicGeometry.Scheme.relativeProj (S.pullback sX)).hom =
        pullback.fst _ _ ≫ P.hom ≫ AlgebraicGeometry.Scheme.affineLineOver.toBase X
      rw [Category.assoc, he₀', ← hW.isoPullback_inv_fst, Category.assoc, ← hfst]
    · intro d
      obtain ⟨ι⟩ := htw d
      have hmor : (hW.isoPullback.symm ≪≫ e₀.symm).hom ≫ e₀.hom ≫ pullback.snd sX P.hom =
          ((AlgebraicGeometry.Scheme.relativeProj S).hom ≫
            AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).fiberι
              (AlgebraicGeometry.Scheme.affineLineOver.point k t) := by
        show (hW.isoPullback.inv ≫ e₀.inv) ≫ e₀.hom ≫ pullback.snd sX P.hom = pullback.fst _ _
        rw [Category.assoc, Iso.inv_hom_id_assoc, hW.isoPullback_inv_fst]
      rw [← hmor]
      exact ⟨((AlgebraicGeometry.Scheme.Modules.pullbackComp _ _).app
        (AlgebraicGeometry.Scheme.relativeProj.twist S d)).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullback _).mapIso ι⟩

end
