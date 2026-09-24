import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.Fiber
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Modules.RestrictToLambda
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01o3

/-! # Fibers of a relative Proj over the affine line

Let `X` be a scheme over a field `k` (any `k`-scheme; no projectivity or locally-weighted-polynomial
hypothesis), `S` a graded quasi-coherent algebra on `X × A¹`, `𝒴 = Proj_{X×A¹} S` and
`f : 𝒴 → X × A¹ → A¹_k`. For every `t ∈ k`, the scheme-theoretic fiber of `f` over the `k`-rational point
`λ = t` is isomorphic over `X` to `Proj_X (S|_{λ=t})` (where `S|_{λ=t}` is the pullback of `S` along the section
`sectionAt t`), and for every `d` the restriction of `O_𝒴(d)` to the fiber corresponds to `O_{Proj S|_{λ=t}}(d)`.

This is the general form of part (c) of `relativeProj_family_over_line`: the locally-weighted-polynomial
hypothesis and `Nonempty σ` there serve only parts (a) and (b); part (c) holds for arbitrary `S`. Both the fiber
at zero (index set empty when `r = 0`) and the fiber at one use this lemma directly; see the family `𝒴 → A¹`
in the proof of Proposition 2.4 of the paper.

Proof (Stacks 01O3 + pasting of pullbacks):
1. The point `point k t` of `A¹_k` is the image of the closed point under the section `s₀ := sectionAt (Spec k) t`
   (`point_eq_sectionAtBase_closedPoint`). By Mathlib's `descResidueField_stalkClosedPointTo_fromSpecResidueField`,
   `s₀ = Spec(ρ) ≫ fromSpecResidueField` with `ρ : κ(point) → k`. `ρ` is injective (a field homomorphism);
   `Spec(ρ)` has the retraction `fromSpecResidueField ≫ toBase` (since `s₀ ≫ toBase = 𝟙`), and `Spec` is fully
   faithful on affine schemes, so `ρ` has a left inverse and is surjective. Hence `ρ` is an isomorphism
   (`exists_residueField_point_iso`).
2. The square `X →(sectionAt t) X×A¹ →(toLine) A¹_k` over `X →(X↘Spec k) Spec k →(s₀) A¹_k` is a pullback: paste
   it horizontally with `AffineSpace.isPullback_map` (`X×A¹ = X ×_{Spec k} A¹_k`); the outer square is the trivial
   pullback of `(𝟙, 𝟙)`, so `IsPullback.of_right` applies (`isPullback_sectionAt_toLine`). Replacing the bottom
   edge by `fromSpecResidueField` (`IsPullback.of_iso` along `Spec(ρ)`) gives a pullback square for
   `(toLine).fiber (point k t)` with vertex `X` (`exists_isPullback_sectionAt_fromSpecResidueField`).
3. For `q : Y → X×A¹`, `(q ≫ toLine).fiber (point k t) = Y ×_{A¹_k} Spec κ`; vertical pasting (`IsPullback.of_bot`)
   gives `IsPullback u fiberι (sectionAt t) q`, i.e. the fiber is `X ×_{X×A¹} Y` (`exists_isPullback_fiber_toLine`).
4. Take `Y = Proj S` and `q` the structure morphism: Stacks 01O3 (`relativeProj_baseChange`) gives
   `Proj_X(S|_{λ=t}) ≅ X ×_{X×A¹} Proj S`, compatible with the projection to `X` and with `O(d)`. Compose the two
   isomorphisms; "over `X`" follows from `sectionAt t ≫ toBase = 𝟙` and the commutativity of the pullback square;
   the correspondence of `O(d)` rewrites the pullback along `fiberι = ι ≫ pullback.snd` with
   `Modules.pullbackComp` / `pullbackCongr`.

Source: Stacks 01O3; the proof of Proposition 2.4 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.affineLineOver

/-- The section `Spec k → A¹_k` at `λ = t` (with `Spec k` regarded as a `k`-scheme via the identity; this is the
instance used in the definition of `point k t`). -/
def sectionAtBase (k : Type u) [Field k] (t : k) :
    AlgebraicGeometry.Spec (CommRingCat.of k) ⟶
      AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  letI : (AlgebraicGeometry.Spec (CommRingCat.of k)).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.CategoryStruct.id _⟩
  AlgebraicGeometry.Scheme.affineLineOver.sectionAt (k := k) (AlgebraicGeometry.Spec (CommRingCat.of k)) t

theorem point_eq_sectionAtBase_closedPoint (k : Type u) [Field k] (t : k) :
    AlgebraicGeometry.Scheme.affineLineOver.point k t =
      AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t (IsLocalRing.closedPoint k) := by
  show (AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t).base ⟨⊥, Ideal.isPrime_bot⟩ =
    (AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t).base (IsLocalRing.closedPoint k)
  congr 1
  exact PrimeSpectrum.ext IsLocalRing.maximalIdeal_eq_bot.symm

theorem sectionAtBase_toBase (k : Type u) [Field k] (t : k) :
    AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t ≫
      AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      CategoryTheory.CategoryStruct.id _ :=
  AlgebraicGeometry.AffineSpace.homOfVector_over _ _

theorem sectionAtBase_appTop_coord (k : Type u) [Field k] (t : k) (i : ULift.{u} (Fin 1)) :
    (AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t).appTop
        (AlgebraicGeometry.AffineSpace.coord (AlgebraicGeometry.Spec (CommRingCat.of k)) i) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv t :=
  AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord _ _ i

theorem sectionAt_toBase {k : Type u} [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (t : k) :
    AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ≫
      AlgebraicGeometry.Scheme.affineLineOver.toBase X = CategoryTheory.CategoryStruct.id X :=
  AlgebraicGeometry.AffineSpace.homOfVector_over _ _

-- `sectionAt_appTop_coord` / `toLine_appTop_coord` carry the suffix `_fiberAtZero` to avoid a clash with the
-- lemmas of the same name in `WeightedFamilyOverLine.lean`.
theorem sectionAt_appTop_coord_fiberAtZero {k : Type u} [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (t : k) (i : ULift.{u} (Fin 1)) :
    (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t).appTop (AlgebraicGeometry.AffineSpace.coord X i) =
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv t) :=
  AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord _ _ i

theorem toLine_appTop_coord_fiberAtZero {k : Type u} [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (i : ULift.{u} (Fin 1)) :
    (AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).appTop
        (AlgebraicGeometry.AffineSpace.coord (AlgebraicGeometry.Spec (CommRingCat.of k)) i) =
      AlgebraicGeometry.AffineSpace.coord X i :=
  AlgebraicGeometry.AffineSpace.map_appTop_coord _ i

theorem toLine_toBase {k : Type u} [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X ≫
        AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Scheme.affineLineOver.toBase X ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  AlgebraicGeometry.AffineSpace.map_over _

/-- `point k t` is a `k`-rational point: its residue field is isomorphic to `k` via `ρ`, and
`Spec(ρ) ≫ fromSpecResidueField = sectionAtBase t`. -/
theorem exists_residueField_point_iso (k : Type u) [Field k] (t : k) :
    ∃ ρ : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).residueField
          (AlgebraicGeometry.Scheme.affineLineOver.point k t) ⟶ CommRingCat.of k,
      IsIso ρ ∧
        AlgebraicGeometry.Spec.map ρ ≫
          (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).fromSpecResidueField
            (AlgebraicGeometry.Scheme.affineLineOver.point k t) =
          AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t := by
  set A := AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) with hA
  have hy : AlgebraicGeometry.Scheme.affineLineOver.point k t =
      AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t (IsLocalRing.closedPoint k) :=
    AlgebraicGeometry.Scheme.affineLineOver.point_eq_sectionAtBase_closedPoint k t
  let ρ' := A.descResidueField
    (AlgebraicGeometry.Scheme.stalkClosedPointTo (AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t))
  have h' : AlgebraicGeometry.Spec.map ρ' ≫ A.fromSpecResidueField _ =
      AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t :=
    AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k A _
  let ρ : A.residueField (AlgebraicGeometry.Scheme.affineLineOver.point k t) ⟶ CommRingCat.of k :=
    (A.residueFieldCongr hy).hom ≫ ρ'
  have hρ : AlgebraicGeometry.Spec.map ρ ≫
      A.fromSpecResidueField (AlgebraicGeometry.Scheme.affineLineOver.point k t) =
      AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t := by
    rw [AlgebraicGeometry.Spec.map_comp, Category.assoc,
      AlgebraicGeometry.Scheme.residueFieldCongr_fromSpecResidueField]
    exact h'
  refine ⟨ρ, ?_, hρ⟩
  -- ρ is an isomorphism: injective (field homomorphism) + surjective (Spec(ρ) has a retraction, Spec is fully faithful)
  have hret : AlgebraicGeometry.Spec.map ρ ≫
      (A.fromSpecResidueField (AlgebraicGeometry.Scheme.affineLineOver.point k t) ≫
        AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k))) =
      CategoryTheory.CategoryStruct.id _ := by
    rw [← Category.assoc, hρ]
    exact AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase_toBase k t
  let σ : CommRingCat.of k ⟶ A.residueField (AlgebraicGeometry.Scheme.affineLineOver.point k t) :=
    AlgebraicGeometry.Spec.preimage
      (A.fromSpecResidueField (AlgebraicGeometry.Scheme.affineLineOver.point k t) ≫
        AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)))
  have hσ : σ ≫ ρ = CategoryTheory.CategoryStruct.id _ := by
    apply AlgebraicGeometry.Spec.map_injective
    rw [AlgebraicGeometry.Spec.map_comp, AlgebraicGeometry.Spec.map_preimage, AlgebraicGeometry.Spec.map_id]
    exact hret
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨RingHom.injective ρ.hom, fun a => ⟨σ.hom a, ?_⟩⟩
  have h := congrArg (fun f => f.hom a) hσ
  simpa using h

/-- The square `X →(sectionAt t) X×A¹ →(toLine) A¹_k` over `X →(X↘Spec k) Spec k →(sectionAtBase t) A¹_k` is a
pullback. -/
theorem isPullback_sectionAt_toLine {k : Type u} [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (t : k) :
    IsPullback (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t)
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X)
      (AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t) := by
  have t' : IsPullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)
      (AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X)
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k))) :=
    (AlgebraicGeometry.AffineSpace.isPullback_map (n := ULift.{u} (Fin 1))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).flip
  refine IsPullback.of_right ?_ ?_ t'
  · rw [AlgebraicGeometry.Scheme.affineLineOver.sectionAt_toBase,
      AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase_toBase]
    exact IsPullback.of_id_fst
  · have h₁ : (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ≫
          AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X) ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) =
        ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
          AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t) ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      rw [Category.assoc, Category.assoc,
        AlgebraicGeometry.Scheme.affineLineOver.toLine_toBase,
        AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase_toBase, Category.comp_id,
        ← Category.assoc, AlgebraicGeometry.Scheme.affineLineOver.sectionAt_toBase, Category.id_comp]
    have h₂ : ∀ i : ULift.{u} (Fin 1),
        (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ≫
          AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).appTop
            (AlgebraicGeometry.AffineSpace.coord (AlgebraicGeometry.Spec (CommRingCat.of k)) i) =
        ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
          AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t).appTop
            (AlgebraicGeometry.AffineSpace.coord (AlgebraicGeometry.Spec (CommRingCat.of k)) i) := by
      intro i
      have e1 : (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ≫
          AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).appTop
            (AlgebraicGeometry.AffineSpace.coord (AlgebraicGeometry.Spec (CommRingCat.of k)) i) =
          (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t).appTop
            (AlgebraicGeometry.AffineSpace.coord X i) :=
        congrArg (fun x => (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t).appTop x)
          (AlgebraicGeometry.Scheme.affineLineOver.toLine_appTop_coord_fiberAtZero X i)
      have e2 : ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
          AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase k t).appTop
            (AlgebraicGeometry.AffineSpace.coord (AlgebraicGeometry.Spec (CommRingCat.of k)) i) =
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
            ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv t) :=
        congrArg (fun x => (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop x)
          (AlgebraicGeometry.Scheme.affineLineOver.sectionAtBase_appTop_coord k t i)
      exact e1.trans ((AlgebraicGeometry.Scheme.affineLineOver.sectionAt_appTop_coord_fiberAtZero X t i).trans e2.symm)
    exact AlgebraicGeometry.AffineSpace.hom_ext h₁ h₂

/-- The fiber square of `toLine` over the `k`-rational point `λ = t` can be taken with vertex `X` (`fiberι`
corresponding to `sectionAt t`). -/
theorem exists_isPullback_sectionAt_fromSpecResidueField {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (t : k) :
    ∃ v : X ⟶ AlgebraicGeometry.Spec
        ((AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).residueField
          (AlgebraicGeometry.Scheme.affineLineOver.point k t)),
      IsPullback (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t) v
        (AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X)
        ((AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).fromSpecResidueField
          (AlgebraicGeometry.Scheme.affineLineOver.point k t)) := by
  obtain ⟨ρ, hρ, hcomp⟩ := AlgebraicGeometry.Scheme.affineLineOver.exists_residueField_point_iso k t
  have := hρ
  refine ⟨(X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ AlgebraicGeometry.Spec.map ρ, ?_⟩
  refine (AlgebraicGeometry.Scheme.affineLineOver.isPullback_sectionAt_toLine X t).of_iso
    (Iso.refl _) (Iso.refl _) (asIso (AlgebraicGeometry.Spec.map ρ)) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom]
    exact hcomp.symm

/-- For `q : Y → X×A¹`, the fiber of `q ≫ toLine` at `λ = t` is the base change of `Y` along `sectionAt t`:
`IsPullback u fiberι (sectionAt t) q`. -/
theorem exists_isPullback_fiber_toLine {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (t : k)
    {Y : AlgebraicGeometry.Scheme.{u}} (q : Y ⟶ AlgebraicGeometry.Scheme.affineLineOver X) :
    ∃ u : (q ≫ AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).fiber
        (AlgebraicGeometry.Scheme.affineLineOver.point k t) ⟶ X,
      IsPullback u
        ((q ≫ AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).fiberι
          (AlgebraicGeometry.Scheme.affineLineOver.point k t))
        (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t) q := by
  obtain ⟨v, hv⟩ :=
    AlgebraicGeometry.Scheme.affineLineOver.exists_isPullback_sectionAt_fromSpecResidueField X t
  have s_out : IsPullback
      ((q ≫ AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).fiberι
        (AlgebraicGeometry.Scheme.affineLineOver.point k t))
      (pullback.snd (q ≫ AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X)
        ((AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).fromSpecResidueField
          (AlgebraicGeometry.Scheme.affineLineOver.point k t)))
      (q ≫ AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X)
      ((AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).fromSpecResidueField
        (AlgebraicGeometry.Scheme.affineLineOver.point k t)) :=
    IsPullback.of_hasPullback _ _
  let u := hv.lift
    ((q ≫ AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).fiberι
        (AlgebraicGeometry.Scheme.affineLineOver.point k t) ≫ q)
    (pullback.snd _ _) (by rw [Category.assoc]; exact s_out.w)
  have hu1 : u ≫ AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t =
      (q ≫ AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).fiberι
        (AlgebraicGeometry.Scheme.affineLineOver.point k t) ≫ q :=
    hv.lift_fst _ _ _
  have hu2 : u ≫ v = pullback.snd _ _ := hv.lift_snd _ _ _
  refine ⟨u, ?_⟩
  apply IsPullback.flip
  refine IsPullback.of_bot ?_ hu1.symm hv
  rw [hu2]
  exact s_out

end AlgebraicGeometry.Scheme.affineLineOver

/-- **Fiber of a relative Proj over the line**: the fiber of `Proj_{X×A¹} S → X×A¹ → A¹_k` over the `k`-rational
point `λ = t` is isomorphic over `X` to `Proj_X (S|_{λ=t})`, with `O(d)` corresponding. Holds for every graded
quasi-coherent algebra `S` (proof in the module docstring). -/
theorem AlgebraicGeometry.Scheme.relativeProj_fiber_over_line {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (S : (AlgebraicGeometry.Scheme.affineLineOver X).GradedQCAlgebra) (t : k) :
    ∃ e : ((AlgebraicGeometry.Scheme.relativeProj S).hom ≫
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
  unfold AlgebraicGeometry.Scheme.GradedQCAlgebra.restrictToLambda
  obtain ⟨u, hu⟩ := AlgebraicGeometry.Scheme.affineLineOver.exists_isPullback_fiber_toLine t
    (AlgebraicGeometry.Scheme.relativeProj S).hom
  obtain ⟨e₀, he₀, htw⟩ := AlgebraicGeometry.Scheme.relativeProj_baseChange
    (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t) S
  let ι := hu.isoPullback
  have hι1 : ι.hom ≫ pullback.fst _ _ = u := hu.isoPullback_hom_fst
  have hι2 : ι.hom ≫ pullback.snd _ _ =
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X).fiberι
          (AlgebraicGeometry.Scheme.affineLineOver.point k t) := hu.isoPullback_hom_snd
  refine ⟨ι ≪≫ e₀.symm, ?_, fun d => ?_⟩
  · have h1 : e₀.inv ≫ (AlgebraicGeometry.Scheme.relativeProj
        (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t))).hom =
        pullback.fst _ _ := by
      rw [← he₀, Iso.inv_hom_id_assoc]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, h1, hι1, ← Category.assoc, ← hu.w, Category.assoc,
      AlgebraicGeometry.Scheme.affineLineOver.sectionAt_toBase, Category.comp_id]
  · obtain ⟨φ⟩ := htw d
    have hsnd : e₀.inv ≫ e₀.hom ≫ pullback.snd (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t)
        (AlgebraicGeometry.Scheme.relativeProj S).hom = pullback.snd _ _ := by
      rw [Iso.inv_hom_id_assoc]
    rw [Iso.trans_hom, Iso.symm_hom]
    exact ⟨((AlgebraicGeometry.Scheme.Modules.pullbackCongr hι2).app _).symm ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp ι.hom (pullback.snd _ _)).app _).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback ι.hom).mapIso
        (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hsnd).app _).symm ≪≫
          ((AlgebraicGeometry.Scheme.Modules.pullbackComp e₀.inv (e₀.hom ≫ pullback.snd _ _)).app _).symm ≪≫
          (AlgebraicGeometry.Scheme.Modules.pullback e₀.inv).mapIso φ) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp ι.hom e₀.inv).app _⟩

end
