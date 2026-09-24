import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineIsoOfFieldIso
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Blowup.PointBlowupFiberIsoProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothRationalCurve

/-! # The exceptional curve of a point blowup is `P¹`

The exceptional curve of the blowup of a smooth surface at a closed point is a smooth rational curve
(Lemma 5.1 of the paper, §5). The proof combines the identification of the fibre
`π⁻¹(p) ≅ P¹_{κ(p)}` over `κ(p)` (Stacks 0AGQ(1), via 0805; `PointBlowupFiberIsoProjectiveLine`) with the
transport of `P¹` along the field isomorphism `κ(p) ≅ k` (`ProjectiveLine.exists_iso_of_fieldIso`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The kernel of a closed immersion with reduced source is a radical ideal sheaf (the same proof as
`MiyaokaMori.PointClosureTransport.ker_eq_radical_of_isReduced`, repeated here to avoid its heavy
import chain). -/
theorem AlgebraicGeometry.Scheme.Hom.ker_eq_radical_of_isReduced' {Y X : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsReduced Y] :
    f.ker = f.ker.radical := by
  ext U x
  have hr : (f.ker.ideal U).IsRadical := by
    rw [AlgebraicGeometry.Scheme.Hom.ker_apply]
    exact (RingHom.ker_isRadical_iff_reduced_of_surjective
      (AlgebraicGeometry.Scheme.Hom.app_surjective f U U.2)).mpr inferInstance
  rw [AlgebraicGeometry.Scheme.IdealSheafData.radical_ideal, Ideal.radical_eq_iff.mpr hr]

/-- **The exceptional curve is `P¹`.** Proof: `F := π.fiber p` is a closed subscheme with underlying set
`π⁻¹{p}`; `pointBlowup.exists_fiber_iso_projectiveLine_residueField` gives `F ≅ P¹_{κ(p)}` over `κ(p)`;
since `k` is algebraically closed and `p` is a closed point, `κ(p) ≅ k` (`residueFieldIsoBase`), and
`ProjectiveLine.exists_iso_of_fieldIso` transports `P¹_{κ(p)}` to `P¹_k`. Hence `F` is integral, so
`ker(F → Bl)` is a radical ideal sheaf, equal to `vanishingIdeal(π⁻¹{p}) = ker(E → Bl)`, and
`IsClosedImmersion.isIso_lift` gives `E ≅ F`; finally the compatibility with the structure morphisms to
`Spec k` is checked piece by piece. -/
theorem exceptional_isSmoothRational {k : Type u} [Field k] [IsAlgClosed k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    (pointBlowup.exceptional S p hp).IsSmoothRational := by
  classical
  set π := pointBlowup.π S p hp with hπ
  have : AlgebraicGeometry.IsClosedImmersion (S.toScheme.fromSpecResidueField p) :=
    AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.mp hp
  have : AlgebraicGeometry.IsClosedImmersion (π.fiberι p) := by
    show AlgebraicGeometry.IsClosedImmersion (pullback.fst π (S.toScheme.fromSpecResidueField p))
    infer_instance
  obtain ⟨e₁, he₁⟩ := pointBlowup.exists_fiber_iso_projectiveLine_residueField S p hp
  have : AlgebraicGeometry.LocallyOfFiniteType
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (S.toVariety.finiteType).toLocallyOfFiniteType
  set ι := AlgebraicGeometry.residueFieldIsoBase
    (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) p hp with hι
  obtain ⟨e₂, he₂⟩ :=
    ProjectiveLine.exists_iso_of_fieldIso (K := S.toScheme.residueField p) (L := k) ι
  have : AlgebraicGeometry.IsIntegral (ProjectiveLine k) :=
    SmoothProjectiveCurve.isIntegral (ProjectiveLine.asSmoothProjectiveCurve k)
  have : AlgebraicGeometry.IsIntegral (π.fiber p) :=
    AlgebraicGeometry.IsIntegral.of_isIso (e₁ ≪≫ e₂).inv
  have hker : (pointBlowup.exceptionalIdeal S p hp).subschemeι.ker = (π.fiberι p).ker := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      AlgebraicGeometry.Scheme.Hom.ker_eq_radical_of_isReduced' (π.fiberι p),
      ← AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support]
    refine congrArg AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ?_
    apply TopologicalSpace.Closeds.ext
    rw [AlgebraicGeometry.Scheme.Hom.support_ker, AlgebraicGeometry.Scheme.Hom.range_fiberι]
    exact ((hp.preimage π.base.hom.continuous).closure_eq).symm
  have hlift := AlgebraicGeometry.IsClosedImmersion.isIso_lift
    (pointBlowup.exceptionalIdeal S p hp).subschemeι (π.fiberι p) hker
  let e₀ : (pointBlowup.exceptional S p hp).carrier ≅ π.fiber p :=
    (asIso (AlgebraicGeometry.IsClosedImmersion.lift
      (pointBlowup.exceptionalIdeal S p hp).subschemeι (π.fiberι p) hker.le)).symm
  have he₀ : e₀.hom ≫ π.fiberι p = (pointBlowup.exceptional S p hp).ι := by
    show inv (AlgebraicGeometry.IsClosedImmersion.lift
      (pointBlowup.exceptionalIdeal S p hp).subschemeι (π.fiberι p) hker.le) ≫ π.fiberι p =
      (pointBlowup.exceptionalIdeal S p hp).subschemeι
    rw [IsIso.inv_comp_eq]
    exact (AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _).symm
  refine ⟨e₀ ≪≫ e₁ ≪≫ e₂, ?_⟩
  have hS : (pointBlowup.exceptional S p hp).carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k) =
      (pointBlowup.exceptional S p hp).ι ≫ π ≫
        (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := rfl
  rw [hS, ← he₀, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, he₂,
    ← Category.assoc e₁.hom, he₁, AlgebraicGeometry.SpecMap_residueFieldIsoBase_inv,
    Category.assoc, ← AlgebraicGeometry.Scheme.Hom.fiber_fac_assoc]

end
