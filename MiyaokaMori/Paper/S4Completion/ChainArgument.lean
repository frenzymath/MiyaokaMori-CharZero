import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.NonconstantMorphism
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.Paper.S4Completion.AdjacentConstantValueAgree
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ConnectedFiniteUnionChain
import MiyaokaMori.Paper.S4Completion.ConstantOnComponent
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.Paper.S4Completion.SectionPointInFiber

/-! # The chain argument

Starting from a fibre component containing `σ(y)`, follow a chain of pairwise meeting components
to the first one on which `Φ` is nonconstant. The components before it are constant, and adjacent
constant components have the same value, so every one of them takes the value `x = Φ(σ(y))`; the
last intersection point therefore gives a point of the nonconstant component mapping to `x`.
This is the chain argument in the proof of Lemma 5.1 of the paper (§5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Along a chain `a :: l` of pairwise meeting components that starts at a component containing a
point over `x` and contains a nonconstant component, some nonconstant component contains a point
over `x`. -/
private lemma first_nonconstant_chain_cons {k : Type u} [Field k]
    {S : SmoothProjectiveSurface k} {X : SmoothProjectiveVariety k}
    {ι : Type} [Fintype ι] {Γ : ι → IntegralCurve k S.toScheme}
    (Φ : S.toScheme ⟶ X.toScheme) (x : X.toScheme) (a : ι) (l : List ι)
    (hchain : (a :: l).IsChain
      (fun i j =>
        (Set.range (Γ i).ι.base ∩ Set.range (Γ j).ι.base).Nonempty))
    (hstart : ∃ p ∈ Set.range (Γ a).ι.base, Φ.base p = x)
    (hmem : ∃ i ∈ a :: l, ¬ IsConstantMorphism ((Γ i).ι ≫ Φ)) :
    ∃ i, ¬ IsConstantMorphism ((Γ i).ι ≫ Φ) ∧
      ∃ p ∈ Set.range (Γ i).ι.base, Φ.base p = x := by
  classical
  cases l with
  | nil =>
      rcases hmem with ⟨i, hi, hni⟩
      simp only [List.mem_singleton] at hi
      subst i
      exact ⟨a, hni, hstart⟩
  | cons b l =>
      have hrel :
          (Set.range (Γ a).ι.base ∩ Set.range (Γ b).ι.base).Nonempty :=
        (List.isChain_cons_cons.mp hchain).1
      have htail : (b :: l).IsChain
          (fun i j =>
            (Set.range (Γ i).ι.base ∩ Set.range (Γ j).ι.base).Nonempty) :=
        (List.isChain_cons_cons.mp hchain).2
      by_cases ha : IsConstantMorphism ((Γ a).ι ≫ Φ)
      · obtain ⟨v, hv⟩ := (isConstantOnWith_iff Φ (Γ a)).mpr ha
        obtain ⟨p, hpa, hpx⟩ := hstart
        have hvx : v = x := (hv p hpa).symm.trans hpx
        obtain ⟨q, hqa, hqb⟩ := hrel
        have hqx : Φ.base q = x := (hv q hqa).trans hvx
        have hmemtail :
            ∃ i ∈ b :: l, ¬ IsConstantMorphism ((Γ i).ι ≫ Φ) := by
          rcases hmem with ⟨i, hi, hni⟩
          simp only [List.mem_cons] at hi
          rcases hi with rfl | hi
          · exact (hni ha).elim
          · exact ⟨i, by simp [hi], hni⟩
        exact first_nonconstant_chain_cons Φ x b l htail
          ⟨q, hqb, hqx⟩ hmemtail
      · exact ⟨a, ha, hstart⟩

/-- **Chain argument.** If the fibre `π⁻¹(y)` is connected and covered by the curves `Γ i`, the section
point `σ(y)` maps to `x`, and `Φ` is nonconstant on some `Γ i`, then there is a component `Γ i` on
which `Φ` is nonconstant and which contains a point mapping to `x`. -/
theorem chain_to_nonconstant {k : Type u} [Field k] {S : SmoothProjectiveSurface k}
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (Φ : S.toScheme ⟶ X.toScheme) (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (σ : C.toScheme ⟶ S.toScheme) (hσ : σ ≫ π = 𝟙 C.toScheme) (y : C.toScheme) (x : X.toScheme)
    (hx : Φ.base (σ.base y) = x)
    {ι : Type} [Fintype ι] {Γ : ι → IntegralCurve k S.toScheme}
    (hcov : (⋃ i, Set.range (Γ i).ι.base) = π.base ⁻¹' {y})
    (hconn : _root_.IsConnected (π.base ⁻¹' {y}))
    (hex : ∃ i, ¬ IsConstantMorphism ((Γ i).ι ≫ Φ)) :
    ∃ i, ¬ IsConstantMorphism ((Γ i).ι ≫ Φ) ∧
      ∃ p ∈ Set.range (Γ i).ι.base, Φ.base p = x := by
  classical
  let T : ι → Set S.toScheme := fun i => Set.range (Γ i).ι.base
  have hcl : ∀ i, IsClosed (T i) := by
    intro i
    exact (Γ i).ι.isClosedEmbedding.isClosed_range
  have hne : ∀ i, (T i).Nonempty := by
    intro i
    exact Set.range_nonempty _
  have hT : (⋃ i, T i) = π.base ⁻¹' {y} := by
    simpa [T] using hcov
  have hconnT : _root_.IsConnected (⋃ i, T i) := by
    rw [hT]
    exact hconn
  obtain ⟨i₀, hi₀⟩ := section_mem_fiber_component π σ hσ y hcov
  obtain ⟨j, hj⟩ := hex
  obtain ⟨l, hlhead, hllast, hlchain⟩ :=
    exists_chain_of_connected T hcl hne hconnT i₀ j
  have hjmem : j ∈ l := by
    have hjopt : j ∈ l.getLast? := by simpa [hllast]
    obtain ⟨hlne, hjeq⟩ := List.mem_getLast?_eq_getLast hjopt
    simpa [hjeq] using (List.getLast_mem hlne)
  cases l with
  | nil => simp at hlhead
  | cons a l =>
      have hai : a = i₀ := by simpa using hlhead
      subst a
      have hstart :
          ∃ p ∈ Set.range (Γ i₀).ι.base, Φ.base p = x :=
        ⟨σ.base y, hi₀, hx⟩
      have hmem :
          ∃ i ∈ i₀ :: l, ¬ IsConstantMorphism ((Γ i).ι ≫ Φ) := by
        exact ⟨j, hjmem, hj⟩
      exact first_nonconstant_chain_cons Φ x i₀ l hlchain hstart hmem

end
