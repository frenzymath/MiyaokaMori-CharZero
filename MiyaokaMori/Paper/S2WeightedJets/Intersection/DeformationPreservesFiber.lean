import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationFiber
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymLocallyWeightedPolynomial

/-! # The deformations preserve the fibers

Over a fixed point `c ∈ C`, the fibers of both deformations are the same weighted projective space with the same
divisible tautological polarization (Lemma 2.3 of the paper: both deformations only change the
transition functions, so the fiber over `c` and `O(m)` on it are unchanged).

Proof outline: both sides are fibers of a `relativeProj`, each identified by
`relativeProj_fiber_weightedProjectiveSpace` with the same weighted projective space `P_{κ(c)}(w)` over `κ(c)`
(`w(i,q) = q+1`), with `O(m)` identified with `weightedProjTwist κ(c) w hw m`; composing the two isomorphisms gives
the fiber isomorphism `e`, and the pullbacks of `O(m)` correspond along `e` (`pullbackComp` / `pullbackCongr` /
`pullbackId` handle `e₁.inv ≫ e₁.hom = 𝟙`). On the `Y_k^GG` side the "locally weighted polynomial" hypothesis is
`hloc`; on the `Y^sp` side it is deduced in `splitWeightedAlgebra_isLocallyWeightedPolynomial` from
`weightedSymAlgebra_isLocallyWeightedPolynomial`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The graded algebra `splitWeightedAlgebraOf F r` of `Y^sp` (the weighted symmetric algebra of one copy of
`⊕_i Q_i` in each weight `1..r`) is locally a weighted polynomial algebra with weights `(i,q) ↦ q+1`.
Proof: each `Q_i` is a line bundle (`F.lineQuotient i`, rank `1`); they are simultaneously trivialized on a common
neighborhood `U` of `c`, so `⊕_i Q_i` is free on `U` and `rankAtStalk (⊕ Q_i) = n+1` everywhere; then apply
`weightedSymAlgebra_isLocallyWeightedPolynomial` with `ρ = n+1`. -/
private theorem splitWeightedAlgebra_isLocallyWeightedPolynomial {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {n r : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) :
    (splitWeightedAlgebraOf F r).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1))
      (fun _ => Nat.succ_pos _) := by
  let Q : Fin r → C.toScheme.Modules := fun _ =>
    CategoryTheory.Limits.biproduct (fun i : Fin (n + 1) =>
      (F.lineQuotient i).toModules)
  let : ∀ q, (Q q).IsLocallyFree := fun q => by
    dsimp [Q]
    infer_instance
  let : ∀ q, (Q q).IsFiniteType := fun q => by
    dsimp [Q]
    infer_instance
  have hQrank : ∀ (q : Fin r) (x : C.toScheme),
      AlgebraicGeometry.Scheme.Modules.rankAtStalk (Q q) x = n + 1 := by
    intro q x
    let P : Fin (n + 1) → C.toScheme.Opens → Prop := fun i U =>
      ∃ I : Type u, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
        ((F.lineQuotient i).toModules) ≅
          SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    have hmono : ∀ (i : Fin (n + 1)) (V U : C.toScheme.Opens), V ≤ U → P i U → P i V := by
      intro i V U hVU h
      obtain ⟨I, ⟨e⟩⟩ := h
      exact ⟨I, AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le
        ((F.lineQuotient i).toModules) hVU I e⟩
    have hex : ∀ i, ∃ U : C.toScheme.Opens, x ∈ U ∧ P i U := by
      intro i
      obtain ⟨U, I, hxU, e⟩ :=
        AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree
          ((F.lineQuotient i).toModules) x
      exact ⟨U, hxU, I, e⟩
    obtain ⟨U, hxU, hU⟩ := AlgebraicGeometry.Scheme.Modules.exists_common_open x P hmono hex
    choose I hI using hU
    have hfin : ∀ i, Finite (I i) := by
      intro i
      exact AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free
        ((F.lineQuotient i).toModules) U (I i) (hI i).some x hxU
    let : ∀ i, Fintype (I i) := fun i => Fintype.ofFinite (I i)
    have eB : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (Q q) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Sigma I) := by
      let e0 : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (Q q) ≅
          CategoryTheory.Limits.biproduct (fun i =>
            (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
              ((F.lineQuotient i).toModules)) :=
        (AlgebraicGeometry.Scheme.Modules.pullback U.ι).mapBiproduct
          (fun i : Fin (n + 1) => (F.lineQuotient i).toModules)
      exact e0 ≪≫ (AlgebraicGeometry.Scheme.Modules.biproduct_iso_free
        (fun i => (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
          ((F.lineQuotient i).toModules)) I (fun i => (hI i).some)).some
    rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
      (Q q) U (Sigma I) eB x hxU]
    have hcard : ∀ i, Fintype.card (I i) = 1 := by
      intro i
      have hline : AlgebraicGeometry.Scheme.Modules.rankAtStalk
          (F.lineQuotient i).toModules x = 1 :=
        ((F.lineQuotient i).rankAtStalk_eq x).trans (F.lineQuotient i).rank_eq_one
      rw [← hline]
      exact (AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
        ((F.lineQuotient i).toModules) U (I i) (hI i).some x hxU).symm
    simp [Fintype.card_sigma, hcard]
  obtain ⟨hS, _⟩ := @AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
    _ r (n + 1) Q (fun _ => inferInstance) (fun _ => inferInstance) hQrank
  simpa [splitWeightedAlgebraOf, Q] using hS

theorem deformations_preserve_fiber {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom]
    (sec : C.toScheme ⟶ Z.left) (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _)
    {n r : ℕ} (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _))
    (F : SubbundleFiltration E (n + 1)) (m : ℤ) (c : C.toScheme) :
    ∃ e : (splitWeightedProjectivization F r).hom.fiber c ≅ (weightedJetProjectivization (k := k) Z sec hs r).hom.fiber c,
      e.hom ≫ (weightedJetProjectivization (k := k) Z sec hs r).hom.fiberToSpecResidueField c =
          (splitWeightedProjectivization F r).hom.fiberToSpecResidueField c ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback ((splitWeightedProjectivization F r).hom.fiberι c)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) m) ≅
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            ((weightedJetProjectivization (k := k) Z sec hs r).hom.fiberι c)).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1 m))) := by
  let σ := ULift.{u} (Fin (n + 1) × Fin r)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  let hw : ∀ i, 0 < w i := fun _ => Nat.succ_pos _
  let : Fintype σ := inferInstance
  obtain ⟨e₁, he₁base, he₁tw⟩ :=
    relativeProj_fiber_weightedProjectiveSpace
      ((jetGradedAlgebra (k := k) Z sec hs r).1) w hw hloc c
  have hsplit := splitWeightedAlgebra_isLocallyWeightedPolynomial (r := r) F
  obtain ⟨e₂, he₂base, he₂tw⟩ :=
    relativeProj_fiber_weightedProjectiveSpace (splitWeightedAlgebraOf F r) w hw hsplit c
  let e := e₂ ≪≫ e₁.symm
  have he₁base' : e₁.inv ≫
        (weightedJetProjectivization (k := k) Z sec hs r).hom.fiberToSpecResidueField c =
      (weightedProjectiveSpace (C.toScheme.residueField c) w hw ↘
        AlgebraicGeometry.Spec (CommRingCat.of (C.toScheme.residueField c))) := by
    rw [← he₁base, Iso.inv_hom_id_assoc]
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, he₁base', he₂base]
  · obtain ⟨h₁⟩ := he₁tw m
    obtain ⟨h₂⟩ := he₂tw m
    let c₁ := (AlgebraicGeometry.Scheme.Modules.pullback e₁.inv).mapIso h₁
    let c₂ := (AlgebraicGeometry.Scheme.Modules.pullbackComp e₁.inv e₁.hom).app
      (weightedProjTwist (C.toScheme.residueField c) w hw m)
    let c₃ := (AlgebraicGeometry.Scheme.Modules.pullbackCongr e₁.inv_hom_id).app
      (weightedProjTwist (C.toScheme.residueField c) w hw m)
    let h₁' : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback e₁.inv).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          ((weightedJetProjectivization (k := k) Z sec hs r).hom.fiberι c)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist
            (jetGradedAlgebra (k := k) Z sec hs r).1 m)) ≅
        (weightedProjTwist (C.toScheme.residueField c) w hw m)) := by
      exact ⟨c₁ ≪≫ c₂ ≪≫ c₃ ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackId _).app
          (weightedProjTwist (C.toScheme.residueField c) w hw m)⟩
    obtain ⟨h₁'⟩ := h₁'
    exact ⟨h₂ ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullback e₂.hom).mapIso h₁').symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp e₂.hom e₁.inv).app _⟩

end
