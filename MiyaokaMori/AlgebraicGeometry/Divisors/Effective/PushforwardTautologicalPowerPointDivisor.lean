import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.VanishingIdealSingletonEqPointIdeal
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveStalkDVR
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveSectionUnitNeighborhood
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.StalkLocalParameterSection

/-! # A closed point of a smooth projective curve is an effective Cartier divisor

The ideal sheaf `I_c = ker(Spec κ(c) → C)` of a closed point `c` of a smooth projective curve is
invertible, so `c` is an effective Cartier divisor. This is used for the fibre degree computation
(`pushforward_taut_pow_eq_fiberDegree`) in the proof of Proposition 2.4 of the paper.

The step "regular everywhere ⇒ global section" does not go through the function field but uses gluing
of sections directly (`objSupIsoProdEqLocus`): see `mem_span_singleton_of_germ_of_isUnit_off_point`.
The description of the kernel ideal sheaf on affine opens does not unfold `Hom.ker` but goes through
`vanishingIdeal_singleton_eq_pointIdeal` (`I_c` is the vanishing ideal sheaf of the closed set `{c}`)
and `vanishingIdeal_ideal`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- The kernel ideal sheaf of a closed point `c` on an affine open `U`: `s ∈ I_c(U)` iff `s ∈ p` for every
`p ∈ Spec Γ(U)` mapping to `c`. -/
theorem mem_ker_fromSpecResidueField_ideal_iff_forall {X : Scheme.{u}} (c : X)
    (hc : IsClosed ({c} : Set X)) (U : X.affineOpens) (s : Γ(X, U)) :
    s ∈ (X.fromSpecResidueField c).ker.ideal U ↔
      ∀ p : PrimeSpectrum Γ(X, U), U.2.fromSpec p = c → s ∈ p.asIdeal := by
  have h := vanishingIdeal_singleton_eq_pointIdeal c hc
  change _ = (X.fromSpecResidueField c).ker at h
  rw [← h, IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  rfl

theorem ker_fromSpecResidueField_ideal_eq_top_of_notMem {X : Scheme.{u}} (c : X)
    (hc : IsClosed ({c} : Set X)) (U : X.affineOpens) (hcU : c ∉ U.1) :
    (X.fromSpecResidueField c).ker.ideal U = ⊤ := by
  rw [Ideal.eq_top_iff_one, mem_ker_fromSpecResidueField_ideal_iff_forall c hc]
  intro p hp
  exact absurd (hp ▸ (U.2.range_fromSpec ▸ Set.mem_range_self p : U.2.fromSpec p ∈ (U.1 : Set X))) hcU

theorem mem_ker_fromSpecResidueField_ideal_iff {X : Scheme.{u}} (c : X)
    (hc : IsClosed ({c} : Set X)) (U : X.affineOpens) (hcU : c ∈ U.1) (s : Γ(X, U)) :
    s ∈ (X.fromSpecResidueField c).ker.ideal U ↔
      X.presheaf.germ U.1 c hcU s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c) := by
  rw [mem_ker_fromSpecResidueField_ideal_iff_forall c hc, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, ← X.mem_basicOpen s c hcU]
  have key : ∀ p : PrimeSpectrum Γ(X, U), s ∈ p.asIdeal ↔ U.2.fromSpec p ∉ X.basicOpen s := by
    intro p
    rw [← not_iff_not, not_not, ← PrimeSpectrum.mem_basicOpen, ← U.2.fromSpec_preimage_basicOpen]
    rfl
  constructor
  · intro H
    have := H (U.2.primeIdealOf ⟨c, hcU⟩) (U.2.fromSpec_primeIdealOf ⟨c, hcU⟩)
    rw [key, U.2.fromSpec_primeIdealOf ⟨c, hcU⟩] at this
    exact this
  · intro H p hp
    rw [key, hp]
    exact H


/-- Gluing lemma: for sections `f, ϖ` on `U`, if the germ of `f` at `c` is a multiple of the germ of `ϖ`
and the germs of `ϖ` at all other points of `U` are units, then `f ∈ (ϖ) ⊆ Γ(X, U)`. Proof: take a
neighbourhood `W₁ ⊆ U` of `c` with `f = ϖ·g` on `W₁`; on `V₂ := D(ϖ)` the section `ϖ` is invertible,
put `g₂ := f/ϖ`; the two agree on `W₁ ∩ V₂` and glue to `G ∈ Γ(U)`, and `f = ϖ·G` by locality. -/
theorem mem_span_singleton_of_germ_of_isUnit_off_point {X : Scheme.{u}} (U : X.Opens) (c : X)
    (hc : c ∈ U) (ϖ f : Γ(X, U))
    (hunit : ∀ y (hy : y ∈ U), y ≠ c → IsUnit (X.presheaf.germ U y hy ϖ))
    (hf : ∃ a, a * X.presheaf.germ U c hc ϖ = X.presheaf.germ U c hc f) :
    f ∈ Ideal.span {ϖ} := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨W, hcW, g, hg⟩ := X.presheaf.exists_germ_eq a
  have hcW' : c ∈ W ⊓ U := ⟨hcW, hc⟩
  have hgt : X.presheaf.germ U c hc f =
      X.presheaf.germ (W ⊓ U) c hcW'
        (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op g *
          X.presheaf.map (homOfLE (inf_le_right : W ⊓ U ≤ U)).op ϖ) := by
    rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, hg, ha]
  obtain ⟨W₁, hcW₁, i₁, i₂, h₁⟩ := X.presheaf.germ_eq c hc hcW' _ _ hgt
  have hW₁U : W₁ ≤ U := i₁.le
  have hW₁W : W₁ ≤ W := i₂.le.trans inf_le_left
  -- f|W₁ = g|W₁ * ϖ|W₁
  have hfW₁ : X.presheaf.map (homOfLE hW₁U).op f =
      X.presheaf.map (homOfLE hW₁W).op g * X.presheaf.map (homOfLE hW₁U).op ϖ := by
    have : X.presheaf.map i₁.op f = X.presheaf.map (homOfLE hW₁U).op f := rfl
    rw [← this, h₁, map_mul, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  -- V₂ := D(ϖ)
  set V₂ := X.basicOpen ϖ with hV₂
  have hV₂U : V₂ ≤ U := X.basicOpen_le ϖ
  have hcover : U ≤ W₁ ⊔ V₂ := by
    intro y hy
    rw [Opens.mem_sup]
    by_cases hyc : y = c
    · subst hyc; exact Or.inl hcW₁
    · exact Or.inr ((X.mem_basicOpen ϖ y hy).mpr (hunit y hy hyc))
  obtain ⟨u, hu⟩ : IsUnit (X.presheaf.map (homOfLE hV₂U).op ϖ) :=
    X.toRingedSpace.isUnit_res_basicOpen ϖ
  -- the two local sections
  let g₁ : Γ(X, W₁) := X.presheaf.map (homOfLE hW₁W).op g
  let g₂ : Γ(X, V₂) := X.presheaf.map (homOfLE hV₂U).op f * (↑u⁻¹ : Γ(X, V₂))
  -- compatibility
  have hcompat : X.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ V₂ ≤ W₁)).op g₁ =
      X.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ V₂ ≤ V₂)).op g₂ := by
    have hZ : W₁ ⊓ V₂ ≤ U := inf_le_left.trans hW₁U
    -- let r be the restriction ring homomorphism to Z
    have e1 : X.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ V₂ ≤ W₁)).op
        (X.presheaf.map (homOfLE hW₁U).op f) = X.presheaf.map (homOfLE hZ).op f := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    have e2 : X.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ V₂ ≤ W₁)).op
        (X.presheaf.map (homOfLE hW₁U).op ϖ) = X.presheaf.map (homOfLE hZ).op ϖ := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    have e3 : X.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ V₂ ≤ V₂)).op
        (X.presheaf.map (homOfLE hV₂U).op f) = X.presheaf.map (homOfLE hZ).op f := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    have e4 : X.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ V₂ ≤ V₂)).op
        (X.presheaf.map (homOfLE hV₂U).op ϖ) = X.presheaf.map (homOfLE hZ).op ϖ := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    have hfZ : X.presheaf.map (homOfLE hZ).op f =
        X.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ V₂ ≤ W₁)).op g₁ *
          X.presheaf.map (homOfLE hZ).op ϖ := by
      rw [← e1, hfW₁, map_mul, e2]
    have huZ : X.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ V₂ ≤ V₂)).op (↑u : Γ(X, V₂)) *
        X.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ V₂ ≤ V₂)).op (↑u⁻¹ : Γ(X, V₂)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    show _ = X.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ V₂ ≤ V₂)).op
        (X.presheaf.map (homOfLE hV₂U).op f * (↑u⁻¹ : Γ(X, V₂)))
    rw [map_mul, e3, hfZ, mul_assoc, ← e4, ← hu, huZ, mul_one]
  -- gluing
  obtain ⟨G₀, hG₀₁, hG₀₂⟩ : ∃ G₀ : Γ(X, W₁ ⊔ V₂),
      X.presheaf.map (homOfLE (le_sup_left : W₁ ≤ W₁ ⊔ V₂)).op G₀ = g₁ ∧
      X.presheaf.map (homOfLE (le_sup_right : V₂ ≤ W₁ ⊔ V₂)).op G₀ = g₂ :=
    ⟨(X.sheaf.objSupIsoProdEqLocus W₁ V₂).inv ⟨(g₁, g₂), hcompat⟩,
      X.sheaf.objSupIsoProdEqLocus_inv_fst W₁ V₂ _,
      X.sheaf.objSupIsoProdEqLocus_inv_snd W₁ V₂ _⟩
  let G : Γ(X, U) := X.presheaf.map (homOfLE hcover).op G₀
  have hG₁ : X.presheaf.map (homOfLE hW₁U).op G = g₁ := by
    rw [← hG₀₁]
    show X.presheaf.map (homOfLE hW₁U).op (X.presheaf.map (homOfLE hcover).op G₀) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hG₂ : X.presheaf.map (homOfLE hV₂U).op G = g₂ := by
    rw [← hG₀₂]
    show X.presheaf.map (homOfLE hV₂U).op (X.presheaf.map (homOfLE hcover).op G₀) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [Ideal.mem_span_singleton']
  refine ⟨G, ?_⟩
  apply X.sheaf.eq_of_locally_eq₂ (homOfLE hW₁U) (homOfLE hV₂U) hcover
  · show X.presheaf.map (homOfLE hW₁U).op (G * ϖ) = X.presheaf.map (homOfLE hW₁U).op f
    rw [map_mul, hG₁, hfW₁]
  · show X.presheaf.map (homOfLE hV₂U).op (G * ϖ) = X.presheaf.map (homOfLE hV₂U).op f
    rw [map_mul, hG₂, ← hu]
    show X.presheaf.map (homOfLE hV₂U).op f * ↑u⁻¹ * ↑u = _
    rw [mul_assoc, Units.inv_mul, mul_one]

end AlgebraicGeometry.Scheme

/-- At a closed point `c` of a smooth projective curve there are an affine open `U ∋ c` and a nonzero
section `ϖ ∈ Γ(C, U)` with `I_c(U) = (ϖ)`.

Proof: a local parameter `ϖ₀` (`AlgebraicGeometry.Divisors.exists_local_parameter_section`; the stalk is a DVR,
`isDiscreteValuationRing_stalk`) has irreducible germ at `c`; `exists_open_isUnit_germ_off_point` shrinks
to a neighbourhood `V` of `c` on which the germs of `ϖ₀` at all points of `V ∖ {c}` are units; shrink
further to an affine open `U ⊆ V` and put `ϖ := ϖ₀|U`.
(`⊇`) `germ_c ϖ` is irreducible, hence not a unit, so `ϖ ∈ I_c(U)` (`mem_ker_fromSpecResidueField_ideal_iff`).
(`⊆`) `f ∈ I_c(U)` gives `germ_c f ∈ m_c = (germ_c ϖ)` (`Irreducible.maximalIdeal_eq`), and the gluing
lemma `mem_span_singleton_of_germ_of_isUnit_off_point` gives `f ∈ (ϖ)`. -/
theorem SmoothProjectiveCurve.exists_affineOpens_ker_ideal_eq_span {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (c : C.carrier) (hc : IsClosed ({c} : Set C.carrier)) :
    ∃ (U : C.carrier.affineOpens) (_ : c ∈ U.1) (ϖ : Γ(C.carrier, U)), ϖ ≠ 0 ∧
      (C.carrier.fromSpecResidueField c).ker.ideal U = Ideal.span {ϖ} := by
  have : AlgebraicGeometry.IsNoetherian C.carrier := by
    have := C.isProper
    have : CompactSpace C.carrier :=
      AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
        (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    exact {}
  have hcoheight : Order.coheight c = 1 :=
    AlgebraicGeometry.Scheme.closedPoint_coheight_eq_one_of_dimension_one C.carrier C.dim_one c hc
  have hdim : topologicalKrullDim C.carrier ≤ 1 := by rw [C.dim_one]
  have : IsDiscreteValuationRing (C.carrier.presheaf.stalk c) :=
    SmoothProjectiveCurve.isDiscreteValuationRing_stalk C c hcoheight
  obtain ⟨U₀, hcU₀, ϖ₀, hirr, -⟩ := AlgebraicGeometry.Divisors.exists_local_parameter_section C.carrier c hcoheight
  have hϖ₀ : ϖ₀ ≠ 0 := by
    intro h
    subst h
    simp at hirr
  obtain ⟨V, hVU₀, hcV, hunit⟩ :=
    AlgebraicGeometry.Scheme.exists_open_isUnit_germ_off_point C.carrier hdim U₀ ϖ₀ hϖ₀ c hcU₀
  obtain ⟨_, ⟨U, hU, rfl⟩, hcU, hUV⟩ :=
    C.carrier.isBasis_affineOpens.exists_subset_of_mem_open hcV V.isOpen
  have hUU₀ : U ≤ U₀ := fun y hy => hVU₀ (hUV hy)
  set ϖ : Γ(C.carrier, U) := C.carrier.presheaf.map (homOfLE hUU₀).op ϖ₀ with hϖ
  have hgerm : ∀ y (hy : y ∈ U), C.carrier.presheaf.germ U y hy ϖ =
      C.carrier.presheaf.germ U₀ y (hUU₀ hy) ϖ₀ :=
    fun y hy => C.carrier.presheaf.germ_res_apply (homOfLE hUU₀) y hy ϖ₀
  have hirr' : Irreducible (C.carrier.presheaf.germ U c hcU ϖ) := by rw [hgerm]; exact hirr
  refine ⟨⟨U, hU⟩, hcU, ϖ, ?_, ?_⟩
  · intro h
    apply hirr'.ne_zero
    rw [h, map_zero]
  · apply le_antisymm
    · intro f hf
      rw [AlgebraicGeometry.Scheme.mem_ker_fromSpecResidueField_ideal_iff c hc ⟨U, hU⟩ hcU,
        hirr'.maximalIdeal_eq, Ideal.mem_span_singleton'] at hf
      exact AlgebraicGeometry.Scheme.mem_span_singleton_of_germ_of_isUnit_off_point U c hcU ϖ f
        (fun y hy hyc => by rw [hgerm]; exact hunit y (hUV hy) hyc) hf
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        AlgebraicGeometry.Scheme.mem_ker_fromSpecResidueField_ideal_iff c hc ⟨U, hU⟩ hcU,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hirr'.not_isUnit

/-- **A closed point is an effective Cartier divisor.** For a closed point `c` of a smooth projective
curve `C` over any field `k`, the ideal sheaf `I_c := ker(Spec κ(c) → C)` of the reduced closed
subscheme is invertible, i.e. there is an effective Cartier divisor `D` with ideal sheaf `I_c`.
Source: Stacks 0B5V (the maximal ideal of a regular one-dimensional local ring is generated by a
nonzerodivisor); this is the point divisor `[y]` of Lemma 5.1 of the paper.

**Proof** (`MiyaokaMori.Statement.IsInvertibleIdeal`: every point has an affine neighbourhood `U` and a
nonzerodivisor `a` with `I(U) = (a)`).
1. For `x ≠ c`: take an affine neighbourhood `U ⊆ C ∖ {c}` of `x` (`{c}` is closed); then
   `I_c(U) = Γ(C, U)` (`ker_fromSpecResidueField_ideal_eq_top_of_notMem`: `I_c` is the vanishing ideal
   sheaf of `{c}` and no point of `Spec Γ(U)` maps to `c`); take `a = 1`.
2. For `x = c`: `exists_affineOpens_ker_ideal_eq_span` gives an affine open `U ∋ c` and `ϖ ≠ 0` with
   `I_c(U) = (ϖ)`; `C` is integral (`SmoothProjectiveCurve.isIntegral`), so `Γ(C, U)` is a domain and `ϖ`
   is a nonzerodivisor.
3. Hence `I_c` is invertible; take `D := ⟨I_c, _⟩ : C.EffCartier` (`= EffectiveCartierDivisor C.carrier`). -/
theorem SmoothProjectiveCurve.exists_effectiveCartierDivisor_point {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (c : C.carrier) (hc : IsClosed ({c} : Set C.carrier)) :
    ∃ D : AlgebraicGeometry.EffectiveCartierDivisor C.carrier,
      D.idealSheaf = (C.carrier.fromSpecResidueField c).ker := by
  refine ⟨⟨(C.carrier.fromSpecResidueField c).ker, ?_⟩, rfl⟩
  intro x
  by_cases hx : x = c
  · subst hx
    obtain ⟨U, hxU, ϖ, hϖ, hI⟩ := SmoothProjectiveCurve.exists_affineOpens_ker_ideal_eq_span C x hc
    have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
    refine ⟨U, hxU, ϖ, fun r hr => ?_, hI⟩
    exact (mul_eq_zero.mp hr).resolve_left hϖ
  · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUc⟩ :=
      C.carrier.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ({c}ᶜ : Set C.carrier) from hx) hc.isOpen_compl
    refine ⟨⟨U, hU⟩, hxU, 1, fun r hr => by simpa using hr, ?_⟩
    rw [Ideal.span_singleton_one,
      AlgebraicGeometry.Scheme.ker_fromSpecResidueField_ideal_eq_top_of_notMem c hc ⟨U, hU⟩
        (fun h => hUc h rfl)]

end
