import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleInterEqIntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackDegreeOnCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RestrictionDegreePositiveOfAmple
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02nx
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierFiniteSupport

/-! # A morphism is constant on a curve iff the pulled-back ample degree vanishes

For an ample line bundle `L`: the restriction of `Φ` to an integral curve `Γ` is constant if and only
if `(Φ^*L)·Γ = 0` (§4 of the paper, proof of Lemma 5.1).

Proof (Stacks 0BET + 0BEV + 02NX):
* `←`: `degree_pullback_restrict` part 1 (constant ⇒ intersection number 0).
* `→`: if `Φ|_Γ` is not constant, `degree_pullback_restrict` part 2 gives an integral curve `R ⊂ X`,
  a dominant `g : Γ → R` with `g ≫ R.ι = Γ.ι ≫ Φ` and `(Φ^*L)·Γ = [K(Γ):K(R)] · (L·R)`.
  - `L·R = deg(L|_R) > 0` (`LineBundle.inter_fundamentalClass_eq_degree`, `degree_restrict_pos_of_ample`).
  - `[K(Γ):K(R)] ≥ 1`: `g` is locally of finite type (cancel `R.ι` from `Γ.ι ≫ Φ`), and the generic point
    of `Γ` is the only point over the generic point of `R` (a second such point `x` would be a closed
    point of the one-dimensional integral `Γ`; `Γ.ι ≫ Φ` is proper hence closed, so `Φ(ι(x))` is a closed
    point of `X` equal to `Φ(ι(η_Γ))`, and by continuity `Φ ∘ ι` maps all of `Γ = closure{η_Γ}` to it,
    i.e. `Φ|_Γ` is constant — contradiction). Stacks 02NX then makes `K(R) → K(Γ)` finite, so the
    `finrank` is positive.
  The product of two positive integers is nonzero, contradicting `(Φ^*L)·Γ = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- In an integral scheme of topological Krull dimension 1, every point other than the generic
point is closed (its coheight is exactly 1, and `AlgebraicGeometry.Intersection.isClosed_singleton_of_coheight_eq_one`
applies). -/
theorem AlgebraicGeometry.isClosed_singleton_of_ne_genericPoint_of_dim_one
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    (hdim : topologicalKrullDim X = 1) {x : X} (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) := by
  apply AlgebraicGeometry.Intersection.isClosed_singleton_of_coheight_eq_one hdim.le x
  let _ : PartialOrder X := specializationOrder X
  have hk : Order.krullDim X = 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  have hle : Order.coheight x ≤ 1 := by
    have h := Order.coheight_le_krullDim x
    rw [hk] at h
    exact WithBot.coe_le_coe.mp h
  have hxη : x < genericPoint X := by
    refine lt_of_le_of_ne ?_ hx
    exact AlgebraicGeometry.Scheme.le_iff_specializes.mpr
      ((genericPoint_spec X).specializes (Set.mem_univ x))
  have hge : Order.coheight (genericPoint X) + 1 ≤ Order.coheight x :=
    Order.coheight_add_one_le hxη
  exact le_antisymm hle (le_trans le_add_self hge)

/-- `functionFieldDegree f = [K(X) : K(Y)]` is positive as soon as the residue-field extension at
the generic point of `X` is finite (`Module.finrank_pos`; the default value `0` of `finrank` is
ruled out by finiteness). -/
theorem functionFieldDegree_pos_of_finite {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y)
    (hfin : (f.residueFieldMap (genericPoint X)).hom.Finite) : 0 < functionFieldDegree f := by
  unfold functionFieldDegree AlgebraicGeometry.Scheme.Hom.residueDegree
  let _ := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  have : Module.Finite (Y.residueField (f.base (genericPoint X)))
      (X.residueField (genericPoint X)) := hfin
  exact Module.finrank_pos

theorem degree_eq_zero_iff_constant {k : Type u} [Field k] [IsAlgClosed k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme) [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper Φ]
    {L : LineBundle X.toVariety} (hL : AlgebraicGeometry.IsAmple L.toModules) (Γ : IntegralCurve k S.toScheme) :
    (Φ ^* L) ⬝ Γ.fundamentalClass = 0 ↔ IsConstantMorphism (Γ.ι ≫ Φ) := by
  obtain ⟨h1, h2⟩ := degree_pullback_restrict Φ L Γ
  refine ⟨fun h0 => ?_, h1⟩
  by_contra hnc
  obtain ⟨R, g, hfac, hg, heq⟩ := h2 hnc
  -- L · R = deg(L|_R) > 0 since L is ample
  have hR : 0 < L ⬝ R.fundamentalClass := by
    rw [LineBundle.inter_fundamentalClass_eq_degree]
    exact degree_restrict_pos_of_ample hL R
  -- g is locally of finite type (cancel the closed immersion R.ι)
  have : AlgebraicGeometry.LocallyOfFiniteType (g ≫ R.ι) := by
    rw [hfac]; infer_instance
  have : AlgebraicGeometry.LocallyOfFiniteType g :=
    AlgebraicGeometry.locallyOfFiniteType_of_comp g R.ι
  -- the generic point of Γ is the only point over the generic point of R
  have hfib : g.base ⁻¹' {g.base (genericPoint Γ.carrier)} = {genericPoint Γ.carrier} := by
    apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      by_contra hxη
      have hxc : IsClosed ({x} : Set Γ.carrier) :=
        AlgebraicGeometry.isClosed_singleton_of_ne_genericPoint_of_dim_one Γ.dim_eq_one hxη
      -- Γ.ι ≫ Φ is proper, hence a closed map
      have hclosed : IsClosed ({(Γ.ι ≫ Φ).base x} : Set X.toScheme) := by
        have := (Γ.ι ≫ Φ).isClosedMap _ hxc
        simpa only [Set.image_singleton] using this
      have hηx : (Γ.ι ≫ Φ).base (genericPoint Γ.carrier) = (Γ.ι ≫ Φ).base x := by
        rw [← hfac]
        simp only [AlgebraicGeometry.Scheme.Hom.comp_apply]
        rw [hx]
      -- Φ ∘ ι maps closure {η_Γ} = Γ into the closed point Φ(ι(x)): it is constant
      apply hnc
      refine ⟨(Γ.ι ≫ Φ).base x, fun z => ?_⟩
      have hz : (Γ.ι ≫ Φ).base (genericPoint Γ.carrier) ⤳ (Γ.ι ≫ Φ).base z :=
        ((genericPoint_spec Γ.carrier).specializes (Set.mem_univ z)).map
          (Γ.ι ≫ Φ).continuous
      rw [hηx] at hz
      exact hz.mem_closed hclosed rfl
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp
  -- Stacks 02NX: K(R) → K(Γ) is finite, so [K(Γ):K(R)] ≥ 1
  have hfin : (g.residueFieldMap (genericPoint Γ.carrier)).hom.Finite :=
    (AlgebraicGeometry.functionField_finite_iff_generic_fiber g hg).mpr hfib
  have hdeg : 0 < functionFieldDegree g := functionFieldDegree_pos_of_finite g hfin
  rw [heq] at h0
  have hpos : 0 < (functionFieldDegree g : ℤ) * (L ⬝ R.fundamentalClass) :=
    mul_pos (by exact_mod_cast hdeg) hR
  exact hpos.ne' h0

end
