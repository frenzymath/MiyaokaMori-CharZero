import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.FiberDegree
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.WeightedProjTopDegree
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjProperLocal
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationFiber

/-! # Positivity of the fiber degree

The fiber degree `v_k` of the relative polarization `B_k = O_{Y_k^GG}(m)` is positive
(Lemma 2.2 of the paper, eq. (2.6)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem fiberDegreePositive_lineBundle_of_iso {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) [M.IsLineBundle] : N.IsLineBundle := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨t⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := M) x
  exact ⟨U, hx, ⟨(AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ t⟩⟩

theorem fiberDegree_pos {k : Type u} [Field k] [IsAlgClosed k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (n r : ℕ) (hr : 1 ≤ r)
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _))
    (m : ℕ) (hm : ((jetGradedAlgebra (k := k) Z sec hs r).1).SufficientlyDivisible m)
    (hdiv : ∀ q ∈ Finset.Icc 1 r, q ∣ m) (c : C.toScheme) (hc : IsClosed ({c} : Set C.toScheme))
    -- The fiber as a `κ(c)`-scheme: Mathlib's `fiberOverSpecResidueField` is a `@[reducible] def`,
    -- not an instance, so it is supplied by an explicit `letI`.
    (hf : letI := ((weightedJetProjectivization (k := k) Z sec hs r).hom).fiberOverSpecResidueField c;
      IsProperOver (C.toScheme.residueField c) (((weightedJetProjectivization (k := k) Z sec hs r).hom).fiber c)) :
    -- `O(m)` is a line bundle: for sufficiently divisible `m` this is `relativeProj.isLineBundle_twist`
    -- (a theorem, not an instance), so the instance argument is passed explicitly.
    0 < @AlgebraicGeometry.relativePolarizationFiberDegree _ _
      (weightedJetProjectivization (k := k) Z sec hs r).hom
      (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ))
      (AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist (jetGradedAlgebra (k := k) Z sec hs r).1 m hm)
      c hf := by
  classical
  let S := (jetGradedAlgebra (k := k) Z sec hs r).1
  let Y := weightedJetProjectivization (k := k) Z sec hs r
  let K : Type u := C.toScheme.residueField c
  let σ : Type u := ULift.{u} (Fin (n + 1) × Fin r)
  let wgt : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  let hw : ∀ i, 0 < wgt i := by
    intro i
    dsimp [wgt]
    omega
  letI : Fintype σ := inferInstance
  letI : Nonempty σ := ⟨ULift.up ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩
  have hS : S.IsLocallyWeightedPolynomial wgt hw := by
    simpa [S, σ, wgt] using hloc
  let eκ : C.toScheme.residueField c ≅ CommRingCat.of k :=
    AlgebraicGeometry.residueFieldIsoBase
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) c hc
  let e : K ≃+* k := by
    simpa [K] using eκ.commRingCatIsoToRingEquiv
  letI : IsAlgClosed K := IsAlgClosed.of_ringEquiv k K e.symm
  letI := Y.hom.fiberOverSpecResidueField c
  obtain ⟨iso, hbase, htwist⟩ := relativeProj_fiber_weightedProjectiveSpace
    S wgt hw hS c
  have hbase' : iso.hom ≫
      (weightedProjectiveSpace K wgt hw ↘
        AlgebraicGeometry.Spec (CommRingCat.of K)) =
      (Y.hom.fiber c ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := by
    change iso.hom ≫
        (weightedProjectiveSpace K wgt hw ↘
          AlgebraicGeometry.Spec (CommRingCat.of K)) =
      (AlgebraicGeometry.Scheme.relativeProj S).hom.fiberToSpecResidueField c
    exact hbase
  let Lrel : Y.left.Modules := AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)
  let Lfib : (Y.hom.fiber c).Modules :=
    (AlgebraicGeometry.Scheme.Modules.pullback (Y.hom.fiberι c)).obj Lrel
  let Lwp : (weightedProjectiveSpace K wgt hw).Modules :=
    weightedProjTwist K wgt hw (m : ℤ)
  letI : Lrel.IsLineBundle :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S m hm
  letI : Lfib.IsLineBundle := inferInstance
  have htw : Nonempty (Lfib ≅
      (AlgebraicGeometry.Scheme.Modules.pullback iso.hom).obj Lwp) := by
    simpa [Lfib, Lrel, Lwp, Y, K] using htwist m
  letI : Lwp.IsLineBundle := by
    obtain ⟨a⟩ := htw
    letI : ((AlgebraicGeometry.Scheme.Modules.pullback iso.hom).obj Lwp).IsLineBundle :=
      fiberDegreePositive_lineBundle_of_iso a
    letI : ((AlgebraicGeometry.Scheme.Modules.pullback iso.inv).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback iso.hom).obj Lwp)).IsLineBundle :=
      inferInstance
    letI : ((AlgebraicGeometry.Scheme.Modules.pullback iso.hom ⋙
        AlgebraicGeometry.Scheme.Modules.pullback iso.inv).obj Lwp).IsLineBundle := by
      change ((AlgebraicGeometry.Scheme.Modules.pullback iso.inv).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback iso.hom).obj Lwp)).IsLineBundle
      infer_instance
    let ciso := (AlgebraicGeometry.Scheme.Modules.pullbackComp iso.inv iso.hom).app Lwp
    let cid := AlgebraicGeometry.Scheme.Modules.pullbackCongr iso.inv_hom_id
    let did := (AlgebraicGeometry.Scheme.Modules.pullbackId
      (weightedProjectiveSpace K wgt hw)).app Lwp
    apply fiberDegreePositive_lineBundle_of_iso (ciso ≪≫ cid.app Lwp ≪≫ did)
  have hproper : IsProperOver K (weightedProjectiveSpace K wgt hw) := by
    letI : AlgebraicGeometry.IsProper
        (weightedProjectiveSpace K wgt hw ↘
          AlgebraicGeometry.Spec (CommRingCat.of K)) := by
      change AlgebraicGeometry.IsProper
        (MiyaokaMori.WeightedJets.weightedProjToSpec K
          (fun i => (⟨wgt i, hw i⟩ : ℕ+)))
      exact MiyaokaMori.WeightedJets.local_weightedProjToSpec_isProper K
        (fun i => (⟨wgt i, hw i⟩ : ℕ+))
    infer_instance
  have htop : AlgebraicGeometry.topSelfIntersection (Y.hom.fiber c) hf Lfib =
      AlgebraicGeometry.topSelfIntersection (weightedProjectiveSpace K wgt hw) hproper Lwp := by
    exact topSelfIntersection_eq_of_iso (k := K) (k' := K)
      (X := Y.hom.fiber c) (X' := weightedProjectiveSpace K wgt hw)
      (L := Lwp) (L₀ := Lfib) (RingEquiv.refl K) iso
      (by simpa using hbase') hf hproper htw
  have hdiv' : ∀ i : σ, wgt i ∣ m := by
    intro i
    apply hdiv (wgt i)
    simp only [Finset.mem_Icc]
    constructor
    · exact Nat.succ_pos _
    · exact Nat.succ_le_of_lt i.down.2.isLt
  have hone : ∃ i : σ, wgt i = 1 := by
    refine ⟨ULift.up ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩, ?_⟩
    rfl
  have hformula := weightedProjectiveSpace_topSelfIntersection K wgt hw hone m hdiv'
    hproper
  have hmpos : 0 < (m : ℤ) := by exact_mod_cast hm.1
  have hpow : 0 < (m : ℤ) ^ (Fintype.card σ - 1) := by
    positivity
  have hweight : ∀ i : σ, 0 < (wgt i : ℤ) := by
    intro i
    exact_mod_cast hw i
  have hprod : 0 < ∏ i, (wgt i : ℤ) := by
    exact Finset.prod_pos fun i hi => hweight i
  have hmul : 0 <
      AlgebraicGeometry.topSelfIntersection (weightedProjectiveSpace K wgt hw)
        hproper Lwp * (∏ i, (wgt i : ℤ)) := by
    rw [hformula]
    exact hpow
  have hwp : 0 < AlgebraicGeometry.topSelfIntersection
      (weightedProjectiveSpace K wgt hw) hproper Lwp := by
    nlinarith
  have hfibdeg : 0 < AlgebraicGeometry.topSelfIntersection
      (Y.hom.fiber c) hf Lfib := by
    rw [htop]
    exact hwp
  simpa [AlgebraicGeometry.relativePolarizationFiberDegree, Lfib, Lrel, Y, S] using hfibdeg

end
