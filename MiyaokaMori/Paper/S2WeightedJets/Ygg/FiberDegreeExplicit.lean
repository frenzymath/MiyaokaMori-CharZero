import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.FiberDegree
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.WeightedProjTopDegree
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjProperLocal
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationFiber

/-! # The explicit fiber degree

The explicit fiber degree of the Veronese polarization (Lemma 2.2 of the paper,
eq. (2.6)):

  v_k = H_k^{(n+1)k-1} · [π_k^{-1}(c)] = 1 / (k!)^{n+1}.

Here `H_k = (1/m) c_1(O(m))`, so with `B = O(m)` and `s = (n+1)k` the statement is

  relativePolarizationFiberDegree Y.hom B c · (k!)^{n+1} = m^{s-1}        (in ℤ),
  relativePolarizationFiberDegree Y.hom B c / m^{s-1} = 1 / (k!)^{n+1}   (in ℚ).

**Proof** (proof of Lemma 2.2 of the paper). The fiber of `Y_k^GG = Proj_C S_k → C` over the closed point `c` is the
weighted projective space `P(w)` over `κ(c) ≅ k` with `w = (1^{n+1}, 2^{n+1}, …, k^{n+1})`
(`relativeProj_fiber_weightedProjectiveSpace`), and `O(m)` restricts to `O_{P(w)}(m)`. Top self-intersection is
invariant under this isomorphism (`topSelfIntersection_eq_of_iso`). On `P(w)` the power map
`φ_k : P^{s-1} → P(w)`, `[u_{i,q}] ↦ [u_{i,q}^q]` is finite of degree `∏ w_i = (k!)^{n+1}` and pulls
`O(m)` back to `O(m)` (`m` divisible by every weight), so the projection formula gives
`(O_{P(w)}(m))^{s-1} · ∏ w_i = (O_{P^{s-1}}(m))^{s-1} = m^{s-1}`; this is
`weightedProjectiveSpace_topSelfIntersection`.
Finally `∏_{(i,q)} q = (k!)^{n+1}` (`weightedJetWeights_prod_eq_factorial_pow`) and
`card σ - 1 = (n+1)k - 1`.

This module is the explicit-value companion of `fiberDegree_pos` (`Paper/S2WeightedJets/Ygg/FiberDegreePositive.lean`),
whose proof reaches the same formula and then only keeps positivity.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem fiberDegreeExplicit_lineBundle_of_iso {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) [M.IsLineBundle] : N.IsLineBundle := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨t⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := M) x
  exact ⟨U, hx, ⟨(AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ t⟩⟩

/-- The product of the jet weights `w = (1^{n+1}, 2^{n+1}, …, r^{n+1})`, indexed by
`ULift (Fin (n+1) × Fin r)` with weight `q + 1` on `(i, q)`, is `(r!)^{n+1}` (proof of Lemma 2.2 of the
paper: `deg φ_k = ∏_{q=1}^k q^{n+1} = (k!)^{n+1}`). -/
theorem weightedJetWeights_prod_eq_factorial_pow (n r : ℕ) :
    ∏ i : ULift.{u} (Fin (n + 1) × Fin r), (((i.down.2 : ℕ) + 1 : ℕ) : ℤ) =
      (r.factorial : ℤ) ^ (n + 1) := by
  have h1 : ∏ j : Fin r, (((j : ℕ) + 1 : ℕ) : ℤ) = (r.factorial : ℤ) := by
    rw [Fin.prod_univ_eq_prod_range (fun j => ((j + 1 : ℕ) : ℤ)) r, ← Nat.cast_prod,
      Finset.prod_range_add_one_eq_factorial]
  calc ∏ i : ULift.{u} (Fin (n + 1) × Fin r), (((i.down.2 : ℕ) + 1 : ℕ) : ℤ)
      = ∏ p : Fin (n + 1) × Fin r, (((p.2 : ℕ) + 1 : ℕ) : ℤ) :=
        Fintype.prod_equiv Equiv.ulift _ _ (fun _ => rfl)
    _ = ∏ a : Fin (n + 1), ∏ b : Fin r, (((b : ℕ) + 1 : ℕ) : ℤ) :=
        Fintype.prod_prod_type _
    _ = ∏ a : Fin (n + 1), (r.factorial : ℤ) := Finset.prod_congr rfl (fun _ _ => h1)
    _ = (r.factorial : ℤ) ^ (n + 1) := by simp

/-- **Explicit fiber degree** (Lemma 2.2 of the paper, eq. (2.6)), integral form:
`v_k · (k!)^{n+1} = m^{(n+1)k-1}` where `v_k = (O(m)|_{fiber})^{(n+1)k-1}` is `relativePolarizationFiberDegree`.
Same hypotheses as `fiberDegree_pos`. -/
theorem fiberDegree_mul_factorial_pow {k : Type u} [Field k] [IsAlgClosed k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (n r : ℕ) (hr : 1 ≤ r)
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _))
    (m : ℕ) (hm : ((jetGradedAlgebra (k := k) Z sec hs r).1).SufficientlyDivisible m)
    (hdiv : ∀ q ∈ Finset.Icc 1 r, q ∣ m) (c : C.toScheme) (hc : IsClosed ({c} : Set C.toScheme))
    (hf : letI := ((weightedJetProjectivization (k := k) Z sec hs r).hom).fiberOverSpecResidueField c;
      IsProperOver (C.toScheme.residueField c) (((weightedJetProjectivization (k := k) Z sec hs r).hom).fiber c)) :
    @AlgebraicGeometry.relativePolarizationFiberDegree _ _
      (weightedJetProjectivization (k := k) Z sec hs r).hom
      (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ))
      (AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist (jetGradedAlgebra (k := k) Z sec hs r).1 m hm)
      c hf * ((r.factorial : ℤ) ^ (n + 1)) = (m : ℤ) ^ ((n + 1) * r - 1) := by
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
      fiberDegreeExplicit_lineBundle_of_iso a
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
    apply fiberDegreeExplicit_lineBundle_of_iso (ciso ≪≫ cid.app Lwp ≪≫ did)
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
  -- the two arithmetic identifications: ∏ w_i = (r!)^{n+1} and card σ = (n+1) r
  have hprod : ∏ i : σ, (wgt i : ℤ) = (r.factorial : ℤ) ^ (n + 1) :=
    weightedJetWeights_prod_eq_factorial_pow n r
  have hcard : Fintype.card σ = (n + 1) * r := by
    simp [σ]
  have hwp : AlgebraicGeometry.topSelfIntersection (weightedProjectiveSpace K wgt hw) hproper Lwp *
      ((r.factorial : ℤ) ^ (n + 1)) = (m : ℤ) ^ ((n + 1) * r - 1) := by
    rw [← hprod, hformula, hcard]
  have hfibdeg : AlgebraicGeometry.topSelfIntersection (Y.hom.fiber c) hf Lfib *
      ((r.factorial : ℤ) ^ (n + 1)) = (m : ℤ) ^ ((n + 1) * r - 1) := by
    rw [htop]
    exact hwp
  exact hfibdeg

/-- **Explicit fiber degree**, rational form used by `harmonic_intersection` (eq. (2.6) of the paper):
`v_k / m^{(n+1)k-1} = 1 / (k!)^{n+1}`, i.e. `H_k^{(n+1)k-1}·[π_k^{-1}(c)] = 1/(k!)^{n+1}` for
`H_k = (1/m) c_1(O(m))`. -/
theorem fiberDegree_div_pow_eq {k : Type u} [Field k] [IsAlgClosed k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (n r : ℕ) (hr : 1 ≤ r)
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _))
    (m : ℕ) (hm : ((jetGradedAlgebra (k := k) Z sec hs r).1).SufficientlyDivisible m)
    (hdiv : ∀ q ∈ Finset.Icc 1 r, q ∣ m) (c : C.toScheme) (hc : IsClosed ({c} : Set C.toScheme))
    (hf : letI := ((weightedJetProjectivization (k := k) Z sec hs r).hom).fiberOverSpecResidueField c;
      IsProperOver (C.toScheme.residueField c) (((weightedJetProjectivization (k := k) Z sec hs r).hom).fiber c)) :
    ((@AlgebraicGeometry.relativePolarizationFiberDegree _ _
      (weightedJetProjectivization (k := k) Z sec hs r).hom
      (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1 (m : ℤ))
      (AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist (jetGradedAlgebra (k := k) Z sec hs r).1 m hm)
      c hf : ℤ) : ℚ) / (m : ℚ) ^ ((n + 1) * r - 1) = 1 / ((r.factorial : ℚ) ^ (n + 1)) := by
  have h := fiberDegree_mul_factorial_pow (k := k) Z sec hs n r hr hloc m hm hdiv c hc hf
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm.1
  have hpow : (m : ℚ) ^ ((n + 1) * r - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hmpos)
  have hfac : ((r.factorial : ℚ) ^ (n + 1)) ≠ 0 := by
    have : (0 : ℚ) < (r.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos r
    exact pow_ne_zero _ (ne_of_gt this)
  rw [div_eq_div_iff hpow hfac, one_mul]
  exact hq

end
