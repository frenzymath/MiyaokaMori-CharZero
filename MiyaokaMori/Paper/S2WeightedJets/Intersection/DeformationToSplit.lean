import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitFamilyFibers
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseGenerationMultiple
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymLocallyWeightedPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeFamilyFiniteRank
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIso
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.RelativeProjLocallyWeightedDimension
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopIntersectionRationalFibers
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedFamilyOverLine
import MiyaokaMori.Algebra.WeightedSymAlgebraCongr
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationOfBundle
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible

/-! # Deformation to the split bundle

Conjugation by `Λ(λ)` gives a deformation of vector bundles `E ⤳ ⊕Q_i`; taking one copy per weight and applying the
flat projective family argument once more, the top self-intersection is unchanged (Lemma 2.3 of
the paper, "splitting the vector bundle").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem gradedQCAlgebra_iso_map_mul_app {X : AlgebraicGeometry.Scheme.{u}}
    {S T : X.GradedQCAlgebra} (φ : S ≅ T) (U : X.Opens) (m n : ℕ)
    (a : S.sectionsPiece U m) (b : S.sectionsPiece U n) :
    (φ.hom.app (m + n)).val.app (Opposite.op U) (S.sectionsGMul U a b) =
      T.sectionsGMul U ((φ.hom.app m).val.app (Opposite.op U) a)
        ((φ.hom.app n).val.app (Opposite.op U) b) := by
  have h := congrArg
    (fun q => q.val.app (Opposite.op U)
      (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) U a b))
    (φ.hom.map_mul m n)
  have h₁ := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
    (φ.hom.app m) (φ.hom.app n) U a b
  have hL : ((S.mul m n ≫ φ.hom.app (m + n)).val.app (Opposite.op U))
      (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) U a b) =
    (φ.hom.app (m + n)).val.app (Opposite.op U) (S.sectionsGMul U a b) := rfl
  have hR : ((MonoidalCategoryStruct.tensorHom (φ.hom.app m) (φ.hom.app n) ≫
      T.mul m n).val.app
      (Opposite.op U))
      (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) U a b) =
    T.sectionsGMul U ((φ.hom.app m).val.app (Opposite.op U) a)
      ((φ.hom.app n).val.app (Opposite.op U) b) := by
    show (T.mul m n).app U ((MonoidalCategoryStruct.tensorHom
      (φ.hom.app m) (φ.hom.app n)).val.app
      (Opposite.op U) (AlgebraicGeometry.Scheme.Modules.tensorSections
        (S.part m) (S.part n) U a b)) = _
    rw [h₁]
    rfl
  exact hL.symm.trans (h.trans hR)

private theorem gradedQCAlgebra_iso_map_one_app {X : AlgebraicGeometry.Scheme.{u}}
    {S T : X.GradedQCAlgebra} (φ : S ≅ T) (U : X.Opens) (r : Γ(X, U)) :
    (φ.hom.app 0).val.app (Opposite.op U) (S.one.app U r) = T.one.app U r := by
  have h := congrArg (fun q => q.val.app (Opposite.op U) r) φ.hom.map_one
  have hL : ((S.one ≫ φ.hom.app 0).val.app (Opposite.op U))
      r = (φ.hom.app 0).val.app (Opposite.op U) (S.one.app U r) := rfl
  exact hL.symm.trans h

private theorem exists_sectionsRing_equiv_of_gradedQCAlgebra_iso
    {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra} (φ : S ≅ T)
    (U : X.Opens) :
    ∃ e : S.sectionsRing U ≃+* T.sectionsRing U,
      (∀ m a, e (DirectSum.of (S.sectionsPiece U) m a) =
        DirectSum.of (T.sectionsPiece U) m ((φ.hom.app m).val.app (Opposite.op U) a)) ∧
      (∀ m a, e.symm (DirectSum.of (T.sectionsPiece U) m a) =
        DirectSum.of (S.sectionsPiece U) m ((φ.inv.app m).val.app (Opposite.op U) a)) ∧
      (∀ r : Γ(X, U), e (S.sectionsUnitHom U r) = T.sectionsUnitHom U r) := by
  let fcomp : ∀ m : ℕ, S.sectionsPiece U m →+ T.sectionsPiece U m := fun m =>
    ((φ.hom.app m).val.app (Opposite.op U)).hom.toAddMonoidHom
  let gcomp : ∀ m : ℕ, T.sectionsPiece U m →+ S.sectionsPiece U m := fun m =>
    ((φ.inv.app m).val.app (Opposite.op U)).hom.toAddMonoidHom
  let f : S.sectionsRing U →+* T.sectionsRing U := DirectSum.toSemiring
    (fun m => (DirectSum.of (T.sectionsPiece U) m).comp (fcomp m)) (by
      show DirectSum.of (T.sectionsPiece U) 0
          (fcomp 0 (S.one.app U (1 : Γ(X, U)))) =
        DirectSum.of (T.sectionsPiece U) 0 (T.one.app U (1 : Γ(X, U)))
      apply congrArg (DirectSum.of (T.sectionsPiece U) 0)
      exact gradedQCAlgebra_iso_map_one_app φ U 1) (by
      intro m n a b
      show DirectSum.of (T.sectionsPiece U) (m + n)
          (fcomp (m + n) (S.sectionsGMul U a b)) =
        DirectSum.of (T.sectionsPiece U) m (fcomp m a) *
          DirectSum.of (T.sectionsPiece U) n (fcomp n b)
      rw [DirectSum.of_mul_of]
      apply congrArg (DirectSum.of (T.sectionsPiece U) (m + n))
      exact gradedQCAlgebra_iso_map_mul_app φ U m n a b)
  let g : T.sectionsRing U →+* S.sectionsRing U := DirectSum.toSemiring
    (fun m => (DirectSum.of (S.sectionsPiece U) m).comp (gcomp m)) (by
      show DirectSum.of (S.sectionsPiece U) 0
          (gcomp 0 (T.one.app U (1 : Γ(X, U)))) =
        DirectSum.of (S.sectionsPiece U) 0 (S.one.app U (1 : Γ(X, U)))
      apply congrArg (DirectSum.of (S.sectionsPiece U) 0)
      exact gradedQCAlgebra_iso_map_one_app φ.symm U 1) (by
      intro m n a b
      show DirectSum.of (S.sectionsPiece U) (m + n)
          (gcomp (m + n) (T.sectionsGMul U a b)) =
        DirectSum.of (S.sectionsPiece U) m (gcomp m a) *
          DirectSum.of (S.sectionsPiece U) n (gcomp n b)
      rw [DirectSum.of_mul_of]
      apply congrArg (DirectSum.of (S.sectionsPiece U) (m + n))
      exact gradedQCAlgebra_iso_map_mul_app φ.symm U m n a b)
  have f_of (m : ℕ) (a : S.sectionsPiece U m) :
      f (DirectSum.of (S.sectionsPiece U) m a) =
        DirectSum.of (T.sectionsPiece U) m (fcomp m a) :=
    DirectSum.toSemiring_of _ _ _ m a
  have g_of (m : ℕ) (a : T.sectionsPiece U m) :
      g (DirectSum.of (T.sectionsPiece U) m a) =
        DirectSum.of (S.sectionsPiece U) m (gcomp m a) :=
    DirectSum.toSemiring_of _ _ _ m a
  have hcomp : g.comp f = RingHom.id _ := by
    apply DirectSum.ringHom_ext
    intro m a
    change g (f (DirectSum.of (S.sectionsPiece U) m a)) =
      DirectSum.of (S.sectionsPiece U) m a
    rw [f_of, g_of]
    have h := congrArg (fun q => q.val.app (Opposite.op U) a)
      (congrArg (fun q : AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom S S => q.app m)
        φ.hom_inv_id)
    exact congrArg (DirectSum.of (S.sectionsPiece U) m) h
  have hcomp' : f.comp g = RingHom.id _ := by
    apply DirectSum.ringHom_ext
    intro m a
    change f (g (DirectSum.of (T.sectionsPiece U) m a)) =
      DirectSum.of (T.sectionsPiece U) m a
    rw [g_of, f_of]
    have h := congrArg (fun q => q.val.app (Opposite.op U) a)
      (congrArg (fun q : AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom T T => q.app m)
        φ.inv_hom_id)
    exact congrArg (DirectSum.of (T.sectionsPiece U) m) h
  let e : S.sectionsRing U ≃+* T.sectionsRing U := {
    toEquiv := {
      toFun := f
      invFun := g
      left_inv := fun x => congrArg (fun q => q x) hcomp
      right_inv := fun x => congrArg (fun q => q x) hcomp' }
    map_mul' := fun x y => map_mul f x y
    map_add' := fun x y => map_add f x y }
  refine ⟨e, ?_, ?_, ?_⟩
  · intro m a
    change f (DirectSum.of (S.sectionsPiece U) m a) = _
    rw [f_of]
    rfl
  · intro m a
    change g (DirectSum.of (T.sectionsPiece U) m a) = _
    rw [g_of]
    rfl
  · intro r
    exact (f_of 0 (S.one.app U r)).trans
      ((congrArg (DirectSum.of (T.sectionsPiece U) 0)
        (gradedQCAlgebra_iso_map_one_app φ U r)).trans rfl)

/-- Being locally a weighted polynomial algebra is transported along an isomorphism of graded algebras: `φ : S ≅ T`
induces on every affine open a graded ring isomorphism `S.sectionsRing U ≃+* T.sectionsRing U` (from `φ.hom.app`
piecewise via `DirectSum.map`, preserving the grading and `sectionsUnit`), and the `equiv`/`equiv_grading`/`equiv_unit`
of the atlas are transported along it. -/
private theorem isLocallyWeightedPolynomial_of_iso {X : AlgebraicGeometry.Scheme.{u}}
    {S T : X.GradedQCAlgebra} (φ : S ≅ T) {σ : Type u} [Finite σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) : T.IsLocallyWeightedPolynomial w hw := by
  obtain ⟨atlas⟩ := hS
  choose e he_fwd he_inv he_unit using
    fun i => exists_sectionsRing_equiv_of_gradedQCAlgebra_iso φ (atlas.chart i).toOpens
  refine ⟨{
    I := atlas.I
    chart := atlas.chart
    covers := atlas.covers
    equiv := fun i => (e i).symm.trans (atlas.equiv i)
    equiv_grading := ?_
    equiv_unit := ?_ }⟩
  · intro i m a
    change a ∈ T.sectionsGrading (atlas.chart i).toOpens m ↔ _
    change a ∈ T.sectionsGrading (atlas.chart i).toOpens m ↔
      (atlas.equiv i ((e i).symm a)).IsWeightedHomogeneous w m
    constructor
    · intro ha
      apply (atlas.equiv_grading i m ((e i).symm a)).mp
      obtain ⟨x, hx⟩ := ha
      refine ⟨(φ.inv.app m).val.app (Opposite.op (atlas.chart i).toOpens) x, ?_⟩
      exact (he_inv i m x).symm.trans (congrArg (e i).symm hx)
    · intro ha
      have hm := (atlas.equiv_grading i m ((e i).symm a)).mpr ha
      obtain ⟨x, hx⟩ := hm
      refine ⟨(φ.hom.app m).val.app (Opposite.op (atlas.chart i).toOpens) x, ?_⟩
      exact (he_fwd i m x).symm.trans
        ((congrArg (e i) hx).trans ((e i).apply_symm_apply a))
  · intro i r
    change (atlas.equiv i ((e i).symm
      (T.sectionsUnitHom (atlas.chart i).toOpens r))) = MvPolynomial.C r
    rw [← he_unit i r, RingEquiv.symm_apply_apply]
    exact atlas.equiv_unit i r

/-- The restriction to `λ = t` of the weighted symmetric algebra of `r` copies of the family `𝒱`: its relative Proj
is isomorphic over `X` to the weighted projectivization of `r` copies of `𝒱|_{λ=t} ≅ V_t`, with `O(d)`
corresponding, and the latter is still locally a weighted polynomial algebra with the same weights. -/
private theorem restrict_side {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {r ρ : ℕ}
    (𝒱 : (AlgebraicGeometry.Scheme.affineLineOver X).Modules)
    (h𝒱lf : ∀ _ : Fin r, 𝒱.IsLocallyFree) (h𝒱ft : ∀ _ : Fin r, 𝒱.IsFiniteType)
    (hrk : ∀ (_ : Fin r) y, AlgebraicGeometry.Scheme.Modules.rankAtStalk 𝒱 y = ρ)
    (t : k) (Vt : X.Modules) (hlf : ∀ _ : Fin r, Vt.IsLocallyFree) (hft : ∀ _ : Fin r, Vt.IsFiniteType)
    (e : SheafOfModules.restrictToLambda 𝒱 t ≅ Vt) :
    ∃ φ : (AlgebraicGeometry.Scheme.relativeProj
          ((@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => 𝒱) h𝒱lf h𝒱ft).restrictToLambda t)).left ≅
        (AlgebraicGeometry.Scheme.relativeProj
          (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => Vt) hlf hft)).left,
      φ.hom ≫ (AlgebraicGeometry.Scheme.relativeProj
          (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => Vt) hlf hft)).hom =
        (AlgebraicGeometry.Scheme.relativeProj
          ((@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => 𝒱) h𝒱lf h𝒱ft).restrictToLambda t)).hom ∧
      (∀ d : ℤ, Nonempty (AlgebraicGeometry.Scheme.relativeProj.twist
          ((@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => 𝒱) h𝒱lf h𝒱ft).restrictToLambda t) d ≅
        (AlgebraicGeometry.Scheme.Modules.pullback φ.hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist
            (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => Vt) hlf hft) d))) ∧
      (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => Vt) hlf hft).IsLocallyWeightedPolynomial
        (fun iq : ULift.{u} (Fin ρ × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _) := by
  obtain ⟨hS, hpb⟩ := @AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
    _ r ρ (fun _ => 𝒱) h𝒱lf h𝒱ft hrk
  obtain ⟨ψ₁⟩ := hpb (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t)
  obtain ⟨ψ₂⟩ := @AlgebraicGeometry.Scheme.weightedSymAlgebra_congr _ r
    (fun _ => (AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t)).obj 𝒱) (fun _ => Vt)
    (fun q => haveI := h𝒱lf q; (AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback
      (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t) 𝒱).1)
    (fun q => haveI := h𝒱ft q; AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback
      (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t) 𝒱)
    hlf hft (fun _ => ⟨e⟩)
  have ψ : (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => 𝒱) h𝒱lf h𝒱ft).restrictToLambda t ≅
      @AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => Vt) hlf hft := ψ₁ ≪≫ ψ₂
  obtain ⟨φ, hφ, htw⟩ := AlgebraicGeometry.Scheme.relativeProj.exists_iso_of_algebra_iso ψ
  refine ⟨φ, hφ, htw, isLocallyWeightedPolynomial_of_iso ψ _ _ ?_⟩
  exact AlgebraicGeometry.Scheme.GradedQCAlgebra.IsLocallyWeightedPolynomial.pullback _ _ _ _ hS

/-- The fiber isomorphism is compatible with the structure morphisms to `Spec k`
(`toBase ≫ (X → Spec k) = toLine ≫ toBase`, `AffineSpace.map_over`). -/
private theorem structure_compat {k : Type u} [Field k] {X Z Y Yt Y' : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (ι : Z ⟶ Y) (π : Y ⟶ AlgebraicGeometry.Scheme.affineLineOver X) (ε : Z ≅ Yt) (πt : Yt ⟶ X)
    (φ : Yt ≅ Y') (π' : Y' ⟶ X)
    (hε : ε.hom ≫ πt = ι ≫ π ≫ AlgebraicGeometry.Scheme.affineLineOver.toBase X)
    (hφ : φ.hom ≫ π' = πt) :
    (ε ≪≫ φ).hom ≫ π' ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      ι ≫ (π ≫ AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X) ≫
        AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  have key : AlgebraicGeometry.Scheme.affineLineOver.toBase X ≫
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X ≫
        AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (AlgebraicGeometry.AffineSpace.map_over (n := ULift.{u} (Fin 1))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).symm
  calc (ε ≪≫ φ).hom ≫ π' ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = (ε.hom ≫ (φ.hom ≫ π')) ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
        simp only [Iso.trans_hom, Category.assoc]
    _ = ι ≫ π ≫ (AlgebraicGeometry.Scheme.affineLineOver.toBase X ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
        rw [hφ, hε]; simp only [Category.assoc]
    _ = _ := by rw [key]; simp only [Category.assoc]

/-- Composition of the correspondences of line bundles under two isomorphisms (`pullbackComp`). -/
private theorem twist_compat {Z Yt Y' : AlgebraicGeometry.Scheme.{u}} (ε : Z ≅ Yt) (φ : Yt ≅ Y')
    (M : Z.Modules) (Mt : Yt.Modules) (M' : Y'.Modules)
    (h1 : Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback ε.hom).obj Mt))
    (h2 : Nonempty (Mt ≅ (AlgebraicGeometry.Scheme.Modules.pullback φ.hom).obj M')) :
    Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback (ε ≪≫ φ).hom).obj M') := by
  obtain ⟨a⟩ := h1
  obtain ⟨b⟩ := h2
  exact ⟨a ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback ε.hom).mapIso b ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp ε.hom φ.hom).app M'⟩

/-- Two relative Proj's over the same base of algebras that are locally weighted polynomial algebras with the same
weights have the same dimension. -/
private theorem dimension_eq_of_locallyWeighted {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pX] (S T : X.GradedQCAlgebra)
    {σ : Type u} [Fintype σ] [Nonempty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) (hT : T.IsLocallyWeightedPolynomial w hw) :
    (AlgebraicGeometry.Scheme.relativeProj S).left.dimension =
      (AlgebraicGeometry.Scheme.relativeProj T).left.dimension := by
  unfold AlgebraicGeometry.Scheme.dimension
  rw [relativeProj_locallyWeighted_krullDim pX S w hw hS,
    relativeProj_locallyWeighted_krullDim pX T w hw hT]

theorem second_deformation_preserves_top_intersection {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {n r : ℕ} (hr : 1 ≤ r) (E : AlgebraicGeometry.VectorBundle C.toVariety)
    (hE : E.rank = n + 1) (F : SubbundleFiltration E (n + 1))
    (m : ℕ) (hm0 : 0 < m) (hmdiv : ∃ c, m = c * ((n + 1) * r * jetWeight r))
    (h₁ : letI : (splitWeightedProjectivization F r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
        ⟨(splitWeightedProjectivization F r).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩;
      IsProperOver k (splitWeightedProjectivization F r).left)
    (h₂ : letI : ((@AlgebraicGeometry.Scheme.weightedProjBundle _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k))) :=
        ⟨(@AlgebraicGeometry.Scheme.weightedProjBundle _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩;
      IsProperOver k (@AlgebraicGeometry.Scheme.weightedProjBundle _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)).left)
    -- on the `Y^sp` side `O(m)` is written as the twist of `splitWeightedAlgebraOf F r`
    -- (`Y^sp := relativeProj (splitWeightedAlgebraOf F r)`, the weighted symmetric algebra of `r` copies of
    -- `⊕_i Q_i`); the invertibility of `O(m)` on both sides is a named instance hypothesis, passed explicitly in
    -- the conclusion
    [hL₁ : (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ)).IsLineBundle]
    [hL₂ : (AlgebraicGeometry.Scheme.relativeProj.twist (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)) (m : ℤ)).IsLineBundle] :
    letI : (splitWeightedProjectivization F r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(splitWeightedProjectivization F r).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : ((@AlgebraicGeometry.Scheme.weightedProjBundle _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k))) :=
      ⟨(@AlgebraicGeometry.Scheme.weightedProjBundle _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩;
    @AlgebraicGeometry.topSelfIntersection k _ (splitWeightedProjectivization F r).left _ h₁
        (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ)) hL₁
      = @AlgebraicGeometry.topSelfIntersection k _ (@AlgebraicGeometry.Scheme.weightedProjBundle _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)).left _ h₂
          (AlgebraicGeometry.Scheme.relativeProj.twist (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)) (m : ℤ)) hL₂ := by
  have : ConnectedSpace C.toScheme := C.connected
  obtain ⟨𝒱, h𝒱lf, ⟨e1⟩, ⟨e0⟩⟩ := bundleFamily_fibers E hE F
  -- the splitting family is only known to be `IsLocallyFree`: finite type and rank follow from the restriction
  -- to `λ = 1` being `≅ E`
  obtain ⟨h𝒱ft, h𝒱rk⟩ :=
    @AlgebraicGeometry.Scheme.Modules.isFiniteType_and_rank_of_restrictToLambda k _ C.toScheme _ _
      𝒱 h𝒱lf (1 : k) E.toModules E.locallyFree E.isFiniteType (n + 1)
      (fun x => (E.rankAtStalk_eq x).trans hE) ⟨e1⟩
  have hQlf : ∀ i : Fin (n + 1), (F.lineQuotient i).toModules.IsLocallyFree :=
    fun i => (F.lineQuotient i).locallyFree
  have hQft : ∀ i : Fin (n + 1), (F.lineQuotient i).toModules.IsFiniteType :=
    fun i => (F.lineQuotient i).isFiniteType
  -- the two ends: `λ = 1 ↦` copies of `E`, `λ = 0 ↦` copies of `⊕ Q_i`
  obtain ⟨φ1, hφ1, htw1, hLWP1⟩ := restrict_side (r := r) (ρ := n + 1) 𝒱 (fun _ => h𝒱lf)
    (fun _ => h𝒱ft) (fun _ y => h𝒱rk y) (1 : k) E.toModules (fun _ => E.locallyFree)
    (fun _ => E.isFiniteType) e1
  obtain ⟨φ0, hφ0, htw0, hLWP0⟩ := restrict_side (r := r) (ρ := n + 1) 𝒱 (fun _ => h𝒱lf)
    (fun _ => h𝒱ft) (fun _ y => h𝒱rk y) (0 : k)
    (CategoryTheory.Limits.biproduct (fun i : Fin (n + 1) => (F.lineQuotient i).toModules))
    (fun _ => inferInstance) (fun _ => inferInstance) e0
  -- the family `𝒴' = Proj Sym_w(𝒱, …, 𝒱) → C × 𝔸¹ → 𝔸¹`
  have hw : ∀ iq : ULift.{u} (Fin (n + 1) × Fin r), ((iq.down.2 : ℕ) + 1) ∈ Finset.Icc 1 r :=
    fun iq => Finset.mem_Icc.mpr ⟨Nat.succ_pos _, iq.down.2.2⟩
  have : Nonempty (ULift.{u} (Fin (n + 1) × Fin r)) := ⟨⟨(0, ⟨0, hr⟩)⟩⟩
  obtain ⟨hS, -⟩ := @AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
    _ r (n + 1) (fun _ => 𝒱) (fun _ => h𝒱lf) (fun _ => h𝒱ft) (fun _ y => h𝒱rk y)
  obtain ⟨hflat, hproj, hfib⟩ := relativeProj_family_over_line (X := C.toScheme) C.projective
    (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => 𝒱) (fun _ => h𝒱lf) (fun _ => h𝒱ft))
    (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) hw hS
  -- `O(m)` is invertible on the family
  have hSD : (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ => 𝒱) (fun _ => h𝒱lf)
      (fun _ => h𝒱ft)).SufficientlyDivisible m := by
    obtain ⟨c, rfl⟩ := hmdiv
    have hc : 0 < c := Nat.pos_of_ne_zero (fun h => by simp [h] at hm0)
    have := veronese_generation_multiple _ _ hw hS c hc
    simpa using this
  have hL := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist _ m hSD
  obtain ⟨ε1, hε1, hεtw1⟩ := hfib 1
  obtain ⟨ε0, hε0, hεtw0⟩ := hfib 0
  exact @topSelfIntersection_eq_of_rational_fibers k _ _ _ hproj hflat _ hL (0 : k) (1 : k) _ _
    ⟨_⟩ ⟨_⟩ h₁ h₂ _ hL₁ _ hL₂
    (ε0 ≪≫ φ0) (structure_compat _ _ ε0 _ φ0 _ hε0 hφ0)
    (twist_compat ε0 φ0 _ _ _ (hεtw0 m) (htw0 m))
    (ε1 ≪≫ φ1) (structure_compat _ _ ε1 _ φ1 _ hε1 hφ1)
    (twist_compat ε1 φ1 _ _ _ (hεtw1 m) (htw1 m))
    (dimension_eq_of_locallyWeighted (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      _ _ _ _ hLWP0 hLWP1)

end
