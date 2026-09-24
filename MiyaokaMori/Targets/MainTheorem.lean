import MiyaokaMori.Paper.S1Intro.DegreeIdentity
import MiyaokaMori.Paper.S2WeightedJets.Cone.MmsetupExists
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.ChooseJetOrder
import MiyaokaMori.Targets.Realization
import MiyaokaMori.Targets.PrescribedPointSpecialization

/-! # The Miyaoka–Mori theorem

**Theorem 1.1** of the paper.** Let `k` be an algebraically closed field of characteristic zero,
`X` a smooth projective variety over `k`, and `f : C → X` a nonconstant morphism from a smooth
connected projective curve over `k`. If `-K_X · f_*[C] > 0`, then for every closed point `x ∈ f(C)`
there is a nonconstant morphism `b : P¹ → X` with `b(0) = x`.

The hypothesis is stated with a canonical divisor, as in the paper: for any Cartier divisor `K` on
`X` with `O_X(K) ≅ ω_X` (`CartierDivisor.IsCanonical X K`), `-K · f_*[C] > 0`. A canonical divisor
exists (`exists_cartierDivisor_lineBundle_iso_canonicalBundle`), so the hypothesis is never vacuous,
and the intersection number does not depend on the choice of `K`
(`intersectionNumber_neg_of_lineBundle_iso_canonicalBundle`). By the degree identity
`-K_X · f_*[C] = deg f^*T_X` (`degree_identity`) the hypothesis is equivalent to `deg f^*T_X > 0`;
`miyaoka_mori_of_pullbackDegree` is the theorem in that form.

Proof: the realization theorem (Theorem 4.2 of the paper, `realization`) produces the
polynomial data and the resolved ruled surface, and the prescribed-point specialization
(Lemma 5.1, `prescribed_point_specialization`) applied at a closed point of `C̃`
over `x` yields the rational curve `b` through `x`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **The Miyaoka–Mori theorem** (Theorem 1.1 of the paper): if `-K_X · f_*[C] > 0` for a
nonconstant morphism `f : C → X` from a smooth connected projective curve, then through every closed
point `x` of `f(C)` there is a nonconstant morphism `b : P¹ → X` with `b(0) = x`. -/
theorem miyaoka_mori {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (X : SmoothProjectiveVariety k) (C : SmoothProjectiveCurve k)
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hf : ¬ IsConstantMorphism f)
    (K : CartierDivisor X.toVariety) (hK : CartierDivisor.IsCanonical X K)
    (hd : 0 < intersectionNumber X (-K) (curveCycleClassPushforward f))
    (x : X.toScheme) (hxc : IsClosed ({x} : Set X.toScheme)) (hx : x ∈ Set.range f.base) :
    ∃ b : ProjectiveLine k ⟶ X.toScheme,
      b.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      ¬ IsConstantMorphism b ∧ b.base (ProjectiveLine.zero k) = x := by
  -- d = -K_X · f_*[C] = deg f^*T_X (the degree identity): recover the tangent-degree form.
  have hdT : 0 < TangentBundle.pullbackDegree f := by
    show 0 < VectorBundle.degree (AlgebraicGeometry.VectorBundle.pullback f (tangentBundle X))
    rw [← degree_identity X C f K hK]
    exact hd
  letI D : MMSetup f := Classical.choice (MMSetup.nonempty f)
  let c : ℚ := 2 * ((X.toVariety.dim : ℚ) + 1) * (D.δ : ℚ) *
      ((LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree : ℚ)
  have hdq : (0 : ℚ) < (TangentBundle.pullbackDegree f : ℚ) := by exact_mod_cast hdT
  obtain ⟨κ, hκ1, hκ⟩ := choose_jet_order c (TangentBundle.pullbackDegree f) hdq
  obtain ⟨ρ, L, jet, r₀, P, S, β, hβ, eW, πS, hπS, σ, Φ,
      hLpos, hjns, hr0eq, hr01, hδr, hPdeg, hPcoord, hPeq,
      hAvoid, hDisj, hproj, hπfac, hconn, -, hσπ, hσβ, hσΦ, hΦover,
      hV, hEmb, hR0bound⟩ :=
    realization f hf hdT κ hκ1 (by simpa [c] using hκ)
  obtain ⟨V, hVopen, hVne, hVfib⟩ := hV
  letI : JacobsonSpace C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let ZC : Set C.toScheme := f.base ⁻¹' {x}
  have hZC : IsClosed ZC := hxc.preimage f.continuous
  have hZCne : ZC.Nonempty := by
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, hc⟩
  obtain ⟨c, hcf, hcc⟩ := nonempty_inter_closedPoints
    (Z := ZC) hZCne hZC.isLocallyClosed
  have hfc : f.base c = x := hcf
  letI : JacobsonSpace ρ.source.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
      (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let Zρ : Set ρ.source.toScheme := ρ.hom.base ⁻¹' {c}
  have hZρ : IsClosed Zρ := hcc.preimage ρ.hom.continuous
  have hZρne : Zρ.Nonempty := by
    obtain ⟨y, hy⟩ := ρ.hom.surjective c
    exact ⟨y, hy⟩
  obtain ⟨y, hyρ, hy⟩ := nonempty_inter_closedPoints
    (Z := Zρ) hZρne hZρ.isLocallyClosed
  have hfy : f.base (ρ.hom.base y) = x := by
    have hyρ' : ρ.hom.base y = c := hyρ
    rw [hyρ']
    exact hfc
  obtain ⟨y₀, hy₀V, hy₀⟩ := exists_closedPoint_mem_open hVopen hVne
  -- Lemma 5.1 at y: a nonconstant k-morphism b : P¹ → X with b(0) = f(ρ(y)) = x
  -- (its degree bound deg b^*O_X(1) ≤ d_F ≤ r₀ is not needed here).
  obtain ⟨b, hbOver, hnc, hb0, -, -⟩ :=
    prescribed_point_specialization f ρ L r₀ S β hβ eW πS hπS σ Φ hAvoid hπfac hσπ hσΦ hΦover
      V hVfib y₀ hy₀V hy₀ y hy
  exact ⟨b, hbOver, hnc, hb0.trans hfy⟩

/-- The Miyaoka–Mori theorem with the hypothesis in the tangent-degree form `d = deg f^*T_X > 0`;
equivalent to `miyaoka_mori` by the degree identity `-K_X · f_*[C] = deg f^*T_X` (`degree_identity`). -/
theorem miyaoka_mori_of_pullbackDegree {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (X : SmoothProjectiveVariety k) (C : SmoothProjectiveCurve k)
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hf : ¬ IsConstantMorphism f)
    (hd : 0 < TangentBundle.pullbackDegree f)
    (x : X.toScheme) (hxc : IsClosed ({x} : Set X.toScheme)) (hx : x ∈ Set.range f.base) :
    ∃ b : ProjectiveLine k ⟶ X.toScheme,
      b.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      ¬ IsConstantMorphism b ∧ b.base (ProjectiveLine.zero k) = x := by
  obtain ⟨K, hK, -⟩ := exists_cartierDivisor_lineBundle_iso_canonicalBundle X
  refine miyaoka_mori X C f hf K hK ?_ x hxc hx
  rw [degree_identity X C f K hK]
  exact hd

end
