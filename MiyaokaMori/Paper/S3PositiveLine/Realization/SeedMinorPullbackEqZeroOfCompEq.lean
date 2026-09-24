import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Realization.ScalarJetFromConstantFiber

/-! # The seed minors pull back to zero where the projectivization agrees with the seed map

Statement: let `P` be a tuple of sections of `A_ρ = ρ^*f^*O_X(1)` on `Tot(L)`, `Φ₀ : U → X` its projectivization
(`IsTupleProjectivization`), and `i : S → U` any `k`-morphism. If `i ≫ Φ₀ = i ≫ U.ι ≫ p_L ≫ ρ ≫ f` (`Φ₀` agrees
along `i` with the seed map `f∘ρ∘p_L`), then every seed minor `M_{ab} = P_a ⊗ s_b − P_b ⊗ s_a` (`s_ℓ = p_L^*ρ^*f_ℓ`)
pulls back to zero along `U.ι` and then `i`.

Proof (the computation for the embedding `i` of a general fiber in `generically_scalar_of_constant_on_generic_fiber`,
extracted for an arbitrary `i`):
1. Seed side: `f ≫ emb = proj(coord)` (`D.hcoord`); pull back four times along `ρ`, `p_L`, `U.ι`, `i`, and use that
   projectivization commutes with pullback, to get `i ≫ U.ι ≫ p_L ≫ ρ ≫ f ≫ emb = proj(i^*U.ι^*p_L^*ρ^*coord)`.
2. `P` side: `Φ₀ ≫ emb = proj(U.ι^*P)` (`hΦ`); pull back once along `i`: `i ≫ Φ₀ ≫ emb = proj(i^*U.ι^*P)`.
3. By hypothesis the two agree, so the minor criterion gives that the `2×2` minors of `i^*U.ι^*P` and
   `i^*U.ι^*(p_L^*ρ^*coord)` vanish.
4. The formula for tensor sections under two pullbacks (`pullbackTensorIso_sectionTensor`) transports this back to
   `i^*U.ι^*(M_{ab}) = 0` (a module isomorphism is injective on global sections).

Source: proof of Theorem 4.2 of the paper (the formal core of "a constant projective map ⇒ the affine
tuple is proportional to the seed tuple").

`sectionPullbackAlong` is the one definition (its body is the adjunction unit) and `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback`
its `Γ`-typed reducible abbrev: `unfold sectionPullbackAlong` does not produce the `Γ`-typed spelling, so the proofs
below use `simp only [sectionPullbackAlong_eq_pullback]` (to reach it) or plain `unfold sectionPullbackAlong` (to reach
the unit). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace SeedMinorPullback

end SeedMinorPullback

open SeedMinorPullback in
/-- Along any `k`-morphism `i : S → U`, if `Φ₀` agrees with the seed map `f∘ρ∘p_L`, the seed minors pull back to zero along `U.ι` and `i`. -/
theorem seedMinor_pullback_eq_zero_of_comp_eq {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety}
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (seedBundlePullback f ρ).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Φ₀ : U.toScheme ⟶ X.toScheme)
    (hΦ : IsTupleProjectivization _ P U Φ₀)
    {S : AlgebraicGeometry.Scheme.{u}} [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (i : S ⟶ U.toScheme) [i.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hconst : i ≫ Φ₀
      = i ≫ U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ ρ.hom ≫ f)
    (a b : Fin (X.embDim + 1)) :
    sectionPullbackAlong i (sectionPullbackAlong U.ι (seedMinor f ρ L D.coord P a b)) = 0 := by
  obtain ⟨hU, hEq⟩ := hΦ
  obtain ⟨hc, hcEq⟩ := D.hcoord
  have : U.ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
  have : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
  have : ρ.hom.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨ρ.isOver⟩
  -- seed side: four pullbacks
  obtain ⟨h1, e1⟩ := exists_projectivizationMorphism_pullback (k := k) ρ.hom
    (seedLineBundle X.embedding f) D.coord hc
  obtain ⟨h2, e2⟩ := exists_projectivizationMorphism_pullback (k := k)
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom _ _ h1
  obtain ⟨h3, e3⟩ := exists_projectivizationMorphism_pullback (k := k) U.ι _ _ h2
  obtain ⟨h4, e4⟩ := exists_projectivizationMorphism_pullback (k := k) i _ _ h3
  -- P side: one pullback
  obtain ⟨h5, e5⟩ := exists_projectivizationMorphism_pullback (k := k) i _ _ hU
  have hR : i ≫ Φ₀ ≫ X.embedding.emb = projectivizationMorphism (k := k) _ _ h4 := by
    rw [← Category.assoc, hconst, ← e4, ← e3, ← e2, ← e1, hcEq]
    simp only [Category.assoc]
  have hproj : projectivizationMorphism (k := k) _ _ h5 = projectivizationMorphism (k := k) _ _ h4 := by
    rw [← e5, ← hEq]
    exact hR
  have hmin := minors_eq_zero_of_projectivizationMorphism_eq (k := k) _ _ _ _ h5 h4 hproj a b
  unfold seedMinor
  rw [sectionPullbackAlong_sub, sectionPullbackAlong_sub, sub_eq_zero]
  apply modules_iso_app_top_injective ((AlgebraicGeometry.Scheme.Modules.pullback i).mapIso
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso U.ι _ _))
  apply modules_iso_app_top_injective (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso i _ _)
  dsimp only [Functor.mapIso_hom]
  have key := fun (s : _) (t : _) => sectionPullbackAlong₂_sectionTensor i U.ι
    (M := (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (seedBundlePullback f ρ).toModules)
    (N := (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj (seedLineBundle X.embedding f))) s t
  rw [key, key]
  exact hmin

end
