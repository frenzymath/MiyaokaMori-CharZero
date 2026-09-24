import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureTransport
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.PushforwardPrincipalDivisorDimensionDrop
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SchemeImageIntegral
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SpecializingMapHeightLe
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02r5
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02rtScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2SchemeLocallyFinite
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a21
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a213
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueDegreeComposition

/-! # Pushforward of a single generator of rational equivalence (Stacks 02S2, scheme version)

The single-generator case of Stacks 02S2 at the level of schemes: `f : X → Y` a proper `k`-morphism between
schemes locally of finite type over a field `k`, and `(w, c)` a 02RW generator on `X`
(`c = (ι_w)_* div_{W}(r)`, `W = closure{w}`, `height w = p+1`); then `f_* c = 0`, or `f_* c` is a generator
on `Y` with generic point `f(w)` (`height f(w) = p+1`).

`X`, `Y` are **not** assumed separated or quasi-compact (the users only have `LocallyOfFiniteType`), so the
point closures `W`, `W'` are not `Variety k`; the 02RT used is the scheme version
(`properPushforward_principalCycle_of_locallyOfFiniteType`), and the dimension theory is Stacks 0A21
(`height_add_coheight_eq_of_locallyOfFiniteType`).

Proof (the three branches of Stacks 02S2, according to `height f(w)`):
1. Let `W := X.pointClosure w`, `g := ι_w ≫ f : W → Y` (proper), `W'' := g.image` the scheme-theoretic image
   of `g` (integral, `isIntegral_image`), `g = g.toImage ≫ g.imageι`, with `g.toImage` proper
   (`IsProper.of_comp`, closed immersions are separated) and dominant. `g.imageι` sends the generic point of
   `W''` to `f(w)`, so `θ : W'' ≅ Y.pointClosure (f w)` (`exists_iso_pointClosure_of_isClosedImmersion`); let
   `p' := g.toImage ≫ θ.hom : W → W' := Y.pointClosure (f w)`, a proper dominant `k`-morphism with
   `p' ≫ ι_{f w} = g`. Hence `f_* c = g_* div(r) = (ι_{f w})_* (p'_* div(r))` (02R5 twice).
2. `dim W = height w = p+1`, `dim W' = height f(w) ≤ height w` (`topologicalKrullDim_pointClosure`; a proper
   morphism is a specialization map).
3. (c) `height f(w) = p+1`: the scheme version of 02RT gives `p'_* div(r) = div(Nm r)`, so
   `f_* c = (ι_{f w})_* div(Nm r)` is a generator.
4. (a)(b) `height f(w) < p+1`: `properPushforward_principalCycle_eq_zero_of_dimension_lt` gives
   `p'_* div(r) = 0`, hence `f_* c = 0`. Here (a) `height f(w) ≤ p−1` is pure dimension counting (`div(r)` is
   supported on points of height `p`, the image points have height `≤ p−1`, and the coefficient convention
   gives `0`), and (b) `height f(w) = p` leaves only the coefficient at the generic point, given by
   `properPushforward_principalCycle_apply_genericPoint_eq_zero` (third paragraph of the proof of Stacks 02S2:
   the generic fiber is a proper integral curve over `κ(η)` on which principal divisors have degree zero,
   02RU). This is assembled here by localizing to an affine open `U ∋ η` of the base `W'` (`V := p⁻¹U`,
   `q := p ∣_ U` is a proper dominant morphism of `k`-varieties, dimensions preserved by Stacks 0A213) and
   applying the variety version `properPushforward_principalDivisor_eq_zero_of_dimension_lt`
   (`PushforwardPrincipalDivisorDimensionDrop.lean`); the three localization lemmas needed (open immersions
   have `residueDegree = 1`, `height` is unchanged on open subschemes, pushforward coefficients localize on
   the base) are proved in this module.

Source: Stacks 02S2 (lemma-proper-pushforward-rational-equivalence), second and third paragraphs of the
proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

section OpenLocalization

variable {k : Type u} [Field k]

/-- An open immersion has residue degree `1` (`residueFieldMap` is an isomorphism). -/
theorem Scheme.Hom.residueDegree_eq_one_of_isOpenImmersion {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (x : U) : f.residueDegree x = 1 := by
  letI : Algebra (X.residueField (f.base x)) (U.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  change Module.finrank (X.residueField (f.base x)) (U.residueField x) = 1
  exact Module.finrank_of_bijective_algebraMap
    ((asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.bijective)

/-- For a nonempty open subscheme `U` of an integral scheme `X` locally of finite type over a field
(`dim X = d`), the `height` of a point (dimension of its closure) is unchanged along `U.ι`. Proof: Stacks 0A21
for `X` and for `U` (`dim U = dim X`, Stacks 0A213), `coheight` is unchanged along open immersions (Mathlib's
`coheight_eq_of_isOpenImmersion`), and the finite `coheight` cancels in `ℕ∞`. -/
theorem Scheme.Opens.height_ι_eq_of_locallyOfFiniteType (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (U : X.Opens) [Nonempty U]
    (x : U.toScheme) : Order.height (U.ι.base x) = Order.height x := by
  letI : U.toScheme.Over (Spec (CommRingCat.of k)) := ⟨U.ι ≫ (X ↘ Spec (CommRingCat.of k))⟩
  haveI : LocallyOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ (X ↘ Spec (CommRingCat.of k))))
  have hdU : topologicalKrullDim U.toScheme = (d : WithBot ℕ∞) := by
    rw [← hd]
    exact topologicalKrullDim_opens_eq_of_irreducible (k := k) X U
      ⟨_, (Nonempty.some (inferInstance : Nonempty U)).2⟩
  have h1 := height_add_coheight_eq_of_locallyOfFiniteType (k := k) X d hd (U.ι.base x)
  have h2 := height_add_coheight_eq_of_locallyOfFiniteType (k := k) U.toScheme d hdU x
  have hco : Order.coheight (U.ι.base x) = Order.coheight x := coheight_eq_of_isOpenImmersion U.ι
  rw [hco] at h1
  have hne : Order.coheight x ≠ ⊤ := by
    intro ht; rw [ht] at h2
    exact absurd h2 (by simp)
  rw [← h2] at h1
  exact ENat.add_left_injective_of_ne_top hne h1

/-- **Localization of pushforward coefficients on the base**: `p : W → W'` proper, `U ⊆ W'` open,
`V := p⁻¹U`, `q := p ∣_ U : V → U`. For `y ∈ U`, `(p_* div_W r)(y) = (q_* div_V(r|_V))(y)`, where `r|_V` is
the image of `r` under the isomorphism of function fields induced by `V.ι`. Proof: both sides are locally
finite sums over the fiber (`properPushforward_apply'`); `V.ι` maps `q⁻¹{y}` bijectively onto `p⁻¹{ι y}`
(`morphismRestrict_ι`), `ord` is unchanged along open immersions (`ord_functionFieldMap`), `height` is
unchanged along open immersions (`height_ι_eq_of_locallyOfFiniteType`, using that `W`, `W'` are locally of
finite type), and residue degrees are handled by `residueDegree_comp` and the degree `1` of open immersions. -/
theorem properPushforward_principalCycle_apply_restrict {W W' : Scheme.{u}}
    [W.Over (Spec (CommRingCat.of k))] [W'.Over (Spec (CommRingCat.of k))]
    [IsIntegral W] [IsIntegral W'] [IsLocallyNoetherian W]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (W' ↘ Spec (CommRingCat.of k))]
    (p : W ⟶ W') [IsProper p] (d d' : ℕ) (hW : topologicalKrullDim W = (d : WithBot ℕ∞))
    (hW' : topologicalKrullDim W' = (d' : WithBot ℕ∞)) (U : W'.Opens) [Nonempty U]
    [Nonempty (p ⁻¹ᵁ U)] (r : W.functionFieldˣ) (y : U.toScheme) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward p (W.principalCycle r) (U.ι.base y) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward (p ∣_ U)
        ((p ⁻¹ᵁ U).toScheme.principalCycle
          (Units.map (MiyaokaMori.OrdOpenImmersion.functionFieldMap (p ⁻¹ᵁ U).ι).toMonoidHom r))
        y := by
  classical
  have hcomp : ∀ v : (p ⁻¹ᵁ U).toScheme, p.base ((p ⁻¹ᵁ U).ι.base v) = U.ι.base ((p ∣_ U).base v) := by
    intro v
    have h1 : p.base ((p ⁻¹ᵁ U).ι.base v) = ((p ⁻¹ᵁ U).ι ≫ p).base v := rfl
    have h2 : U.ι.base ((p ∣_ U).base v) = ((p ∣_ U) ≫ U.ι).base v := rfl
    rw [h1, h2, morphismRestrict_ι]
  rw [properPushforward_apply', properPushforward_apply']
  have himg : p.base ⁻¹' {U.ι.base y} = (p ⁻¹ᵁ U).ι.base '' ((p ∣_ U).base ⁻¹' {y}) := by
    ext x
    constructor
    · intro hx
      have hx' : p.base x = U.ι.base y := hx
      have hxV : x ∈ p ⁻¹ᵁ U := by
        show p.base x ∈ U
        rw [hx']
        exact y.2
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      show (p ∣_ U).base ⟨x, hxV⟩ = y
      apply U.ι.isOpenEmbedding.injective
      rw [← hcomp ⟨x, hxV⟩]
      exact hx'
    · rintro ⟨v, hv, rfl⟩
      have hv' : (p ∣_ U).base v = y := hv
      show p.base ((p ⁻¹ᵁ U).ι.base v) = U.ι.base y
      rw [hcomp v, hv']
  rw [himg, finsum_mem_image (Set.injOn_of_injective (p ⁻¹ᵁ U).ι.isOpenEmbedding.injective)]
  refine finsum_mem_congr rfl fun v hv => ?_
  have hv' : (p ∣_ U).base v = y := hv
  have hord := MiyaokaMori.OrdOpenImmersion.ord_functionFieldMap (p ⁻¹ᵁ U).ι (r : W.functionField) v
  rw [Scheme.principalCycle_apply, Scheme.principalCycle_apply, Units.coe_map,
    show ((MiyaokaMori.OrdOpenImmersion.functionFieldMap (p ⁻¹ᵁ U).ι).toMonoidHom
        (r : W.functionField)) =
      MiyaokaMori.OrdOpenImmersion.functionFieldMap (p ⁻¹ᵁ U).ι (r : W.functionField) from rfl,
    hord]
  congr 2
  simp only [AlgebraicCycle.mapCoeff]
  have h1 : Order.height ((p ⁻¹ᵁ U).ι.base v) = Order.height v :=
    Scheme.Opens.height_ι_eq_of_locallyOfFiniteType (k := k) W d hW (p ⁻¹ᵁ U) v
  have h2 : Order.height (p.base ((p ⁻¹ᵁ U).ι.base v)) = Order.height ((p ∣_ U).base v) := by
    rw [hcomp v]
    exact Scheme.Opens.height_ι_eq_of_locallyOfFiniteType (k := k) W' d' hW' U _
  have h3 : p.residueDegree ((p ⁻¹ᵁ U).ι.base v) = (p ∣_ U).residueDegree v := by
    have e1 := AlgebraicGeometry.Intersection.residueDegree_comp (p ⁻¹ᵁ U).ι p v
    have e2 := AlgebraicGeometry.Intersection.residueDegree_comp (p ∣_ U) U.ι v
    rw [morphismRestrict_ι, e1, Scheme.Hom.residueDegree_eq_one_of_isOpenImmersion (p ⁻¹ᵁ U).ι v,
      Scheme.Hom.residueDegree_eq_one_of_isOpenImmersion U.ι ((p ∣_ U).base v), mul_one,
      one_mul] at e2
    exact e2
  rw [h1, h2, h3]

end OpenLocalization

/-- **Third paragraph of the proof of Stacks 02S2 (scheme version)**: `W`, `W'` integral schemes locally of
finite type over a field `k`, `dim W = d+1`, `dim W' = d`, `p : W → W'` a proper dominant `k`-morphism,
`r ∈ R(W)^×`; then the coefficient of `p_* div_W(r)` at the generic point `η` of `W'` is zero.

**Proof (localize to an affine open of the base, then use the variety version):**
1. Take an affine open `η ∈ U ⊆ W'`, `V := p⁻¹U ∋ η_W`, `q := p ∣_ U : V → U`. `q` is proper (Mathlib instance)
   and dominant (`q η_V = η_U`).
2. `U`, `V` are `k`-varieties: `U` is affine, so `U → Spec k` is affine, separated and of finite type;
   `V → Spec k = q ≫ (U → Spec k)` is a composite of separated morphisms of finite type.
   `dim V = dim W = d+1`, `dim U = dim W' = d` (Stacks 0A213, `topologicalKrullDim_opens_eq_of_irreducible`).
3. The variety version `properPushforward_principalDivisor_eq_zero_of_dimension_lt`
   (`PushforwardPrincipalDivisorDimensionDrop.lean`, i.e. the third paragraph of Stacks 02S2 + 02RU through
   the generic fiber) gives `q_* div_V(r|_V) = 0`.
4. `properPushforward_principalCycle_apply_restrict`: `(p_* div_W r)(η) = (q_* div_V(r|_V))(η_U) = 0`. -/
theorem properPushforward_principalCycle_apply_genericPoint_eq_zero {k : Type u} [Field k]
    {W W' : Scheme.{u}} [W.Over (Spec (CommRingCat.of k))] [W'.Over (Spec (CommRingCat.of k))]
    [IsIntegral W] [IsIntegral W'] [IsLocallyNoetherian W] [IsLocallyNoetherian W']
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (W' ↘ Spec (CommRingCat.of k))]
    (p : W ⟶ W') [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    (hp : p.base (genericPoint W) = genericPoint W')
    (d : ℕ) (hW : topologicalKrullDim W = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hW' : topologicalKrullDim W' = (d : WithBot ℕ∞)) (r : W.functionFieldˣ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward p (W.principalCycle r) (genericPoint W') = 0 := by
  classical
  -- 1. an affine open `U ∋ η`
  obtain ⟨U, hU, hηU⟩ : ∃ U : W'.Opens, IsAffineOpen U ∧ genericPoint W' ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := W'.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint W')) isOpen_univ
    exact ⟨U, hU, hxU⟩
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  set V := p ⁻¹ᵁ U with hVdef
  have hηV : genericPoint W ∈ V := by
    show p.base (genericPoint W) ∈ U
    rw [hp]; exact hηU
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  let q : V.toScheme ⟶ U.toScheme := p ∣_ U
  have hgenU : U.ι.base (genericPoint U.toScheme) = genericPoint W' :=
    genericPoint_eq_of_isOpenImmersion U.ι
  have hgenV : V.ι.base (genericPoint V.toScheme) = genericPoint W :=
    genericPoint_eq_of_isOpenImmersion V.ι
  have hq : q.base (genericPoint V.toScheme) = genericPoint U.toScheme := by
    apply U.ι.isOpenEmbedding.injective
    have h1 : U.ι.base (q.base (genericPoint V.toScheme)) = (q ≫ U.ι).base (genericPoint V.toScheme) :=
      rfl
    rw [hgenU, h1]
    show ((p ∣_ U) ≫ U.ι).base (genericPoint V.toScheme) = genericPoint W'
    rw [morphismRestrict_ι]
    have h2 : (V.ι ≫ p).base (genericPoint V.toScheme) = p.base (V.ι.base (genericPoint V.toScheme)) :=
      rfl
    rw [h2, hgenV, hp]
  -- 2. the `k`-variety structures
  haveI : IsAffine U.toScheme := hU
  letI : U.toScheme.Over (Spec (CommRingCat.of k)) := ⟨U.ι ≫ (W' ↘ Spec (CommRingCat.of k))⟩
  letI : V.toScheme.Over (Spec (CommRingCat.of k)) := ⟨V.ι ≫ (W ↘ Spec (CommRingCat.of k))⟩
  haveI : IsSeparated (U.toScheme ↘ Spec (CommRingCat.of k)) := inferInstance
  haveI : QuasiCompact (U.toScheme ↘ Spec (CommRingCat.of k)) := inferInstance
  haveI : LocallyOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ (W' ↘ Spec (CommRingCat.of k))))
  haveI : IsOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of k)) := ⟨⟩
  haveI : IsProper q := inferInstance
  haveI : q.IsOver (Spec (CommRingCat.of k)) := ⟨by
    show q ≫ (U.ι ≫ (W' ↘ Spec (CommRingCat.of k))) = V.ι ≫ (W ↘ Spec (CommRingCat.of k))
    rw [← Category.assoc]
    show ((p ∣_ U) ≫ U.ι) ≫ (W' ↘ Spec (CommRingCat.of k)) = V.ι ≫ (W ↘ Spec (CommRingCat.of k))
    rw [morphismRestrict_ι, Category.assoc, comp_over p]⟩
  haveI : IsSeparated (V.toScheme ↘ Spec (CommRingCat.of k)) := by
    have : IsSeparated (q ≫ (U.toScheme ↘ Spec (CommRingCat.of k))) := inferInstance
    rwa [comp_over q] at this
  haveI : LocallyOfFiniteType (V.toScheme ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ (W ↘ Spec (CommRingCat.of k))))
  haveI : QuasiCompact (V.toScheme ↘ Spec (CommRingCat.of k)) := by
    have : QuasiCompact (q ≫ (U.toScheme ↘ Spec (CommRingCat.of k))) := inferInstance
    rwa [comp_over q] at this
  haveI : IsOfFiniteType (V.toScheme ↘ Spec (CommRingCat.of k)) := ⟨⟩
  let VVar : Variety k := { carrier := V.toScheme }
  let UVar : Variety k := { carrier := U.toScheme }
  -- dimensions
  have hdimV : topologicalKrullDim V.toScheme = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hW]
    exact topologicalKrullDim_opens_eq_of_irreducible (k := k) W V ⟨_, hηV⟩
  have hdimU : topologicalKrullDim U.toScheme = (d : WithBot ℕ∞) := by
    rw [← hW']
    exact topologicalKrullDim_opens_eq_of_irreducible (k := k) W' U ⟨_, hηU⟩
  have hdV : V.toScheme.dimension = d + 1 := by
    unfold Scheme.dimension
    rw [hdimV]
    exact ENat.toNat_natCast _
  have hdU : U.toScheme.dimension = d := by
    unfold Scheme.dimension
    rw [hdimU]
    exact ENat.toNat_natCast _
  have hdim : UVar.toScheme.dimension < VVar.toScheme.dimension := by
    show U.toScheme.dimension < V.toScheme.dimension
    omega
  -- 3. the variety version
  let r' : V.toScheme.functionFieldˣ :=
    Units.map (MiyaokaMori.OrdOpenImmersion.functionFieldMap V.ι).toMonoidHom r
  have h0 := properPushforward_principalDivisor_eq_zero_of_dimension_lt (W := VVar) (W' := UVar)
    q hq hdim r'
  have h1 : AlgebraicGeometry.AlgebraicCycle.properPushforward q (V.toScheme.principalCycle r')
      (genericPoint U.toScheme) = 0 := by
    have := congrArg (fun c : AlgebraicCycle U.toScheme ℤ => c (genericPoint U.toScheme)) h0
    exact this
  -- 4. localization
  rw [← hgenU, properPushforward_principalCycle_apply_restrict (k := k) p (d + 1) d hW hW' U r]
  exact h1

/-- **The dimension-drop case of Stacks 02S2 (scheme version)**: `p_* div_W(r) = 0` when `dim W' < dim W`.
`dim W' ≤ dim W − 2` is pure dimension counting; for `dim W' = dim W − 1` only the coefficient at the generic
point remains, given by `properPushforward_principalCycle_apply_genericPoint_eq_zero`. -/
theorem properPushforward_principalCycle_eq_zero_of_dimension_lt {k : Type u} [Field k]
    {W W' : Scheme.{u}} [W.Over (Spec (CommRingCat.of k))] [W'.Over (Spec (CommRingCat.of k))]
    [IsIntegral W] [IsIntegral W'] [IsLocallyNoetherian W] [IsLocallyNoetherian W']
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (W' ↘ Spec (CommRingCat.of k))]
    (p : W ⟶ W') [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    (hp : p.base (genericPoint W) = genericPoint W')
    (d d' : ℕ) (hW : topologicalKrullDim W = (d : WithBot ℕ∞))
    (hW' : topologicalKrullDim W' = (d' : WithBot ℕ∞)) (hlt : d' < d) (r : W.functionFieldˣ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward p (W.principalCycle r) = 0 := by
  ext z
  by_contra hz
  change AlgebraicGeometry.AlgebraicCycle.properPushforward p (W.principalCycle r) z ≠ 0 at hz
  obtain ⟨x, hxz, hcx, hht⟩ := exists_of_properPushforward_apply_ne_zero p _ hz
  -- `ord_x r ≠ 0 ⇒ coheight x = 1 ⇒ height x + 1 = d`
  have hco : Order.coheight x = 1 := by
    by_contra h
    exact hcx (Scheme.ord_eq_zero_of_coheight_neq_one h _)
  have h1 := height_add_coheight_eq_of_locallyOfFiniteType (k := k) W d hW x
  have h2 := height_add_coheight_eq_of_locallyOfFiniteType (k := k) W' d' hW' z
  rw [hco] at h1
  rw [← hht] at h2
  -- `height x` is a natural number `m` with `m + 1 = d`, `m ≤ d'`
  have hne : Order.height x ≠ ⊤ := by
    intro ht; rw [ht] at h1
    exact absurd h1 (by simp)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hm] at h1 h2
  have hmd : m + 1 = d := by exact_mod_cast h1
  have hmle : m ≤ d' := by
    have : (m : ℕ∞) ≤ (d' : ℕ∞) := h2 ▸ le_self_add
    exact_mod_cast this
  have hd' : m = d' := by omega
  subst hd'
  -- `coheight z = 0`, so `z` is the generic point
  have hcoz : Order.coheight z = 0 := by
    have h3 : ((m : ℕ) : ℕ∞) + Order.coheight z = ((m : ℕ) : ℕ∞) + 0 := by rw [h2, add_zero]
    exact ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top _) h3
  have hzη : z = genericPoint W' := by
    have hmax : IsMax z := Order.coheight_eq_zero.mp hcoz
    have hz1 : genericPoint W' ⤳ z := genericPoint_specializes z
    have hz2 : z ⤳ genericPoint W' := hmax (b := genericPoint W') hz1
    exact (hz2.antisymm hz1).eq
  subst hzη
  exact hz (properPushforward_principalCycle_apply_genericPoint_eq_zero (k := k) p hp m
    (by rw [hW, hmd]) hW' r)

/-- Equal morphisms have equal pushforwards (avoiding a dependent rewrite of the `IsProper` instance). -/
private theorem properPushforward_congr' {W X : Scheme.{u}} {f g : W ⟶ X} (h : f = g) [IsProper f]
    [IsProper g] (c : AlgebraicCycle W ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f c = AlgebraicGeometry.AlgebraicCycle.properPushforward g c := by
  subst h; rfl

/-- A dominant morphism sends the generic point to the generic point. -/
theorem Scheme.Hom.base_genericPoint_of_isDominant {W W' : Scheme.{u}} [IsIntegral W]
    [IsIntegral W'] (q : W ⟶ W') [IsDominant q] :
    q.base (genericPoint W) = genericPoint W' := by
  have h1 := (genericPoint_spec W).image q.continuous
  rw [Set.image_univ, q.denseRange.closure_range] at h1
  exact h1.eq (genericPoint_spec _)

/-- **The single-generator case of Stacks 02S2 (scheme version).** -/
theorem properPushforward_eq_zero_or_isRatEquivGen {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))] [IsProper f]
    (p : ℕ) (w : X) (c : AlgebraicCycle X ℤ) (h : IsRatEquivGen X p w c) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f c = 0 ∨
      IsRatEquivGen Y p (f.base w) (AlgebraicGeometry.AlgebraicCycle.properPushforward f c) := by
  classical
  obtain ⟨hw, hint, hci, hLN, r, rfl⟩ := h
  let S := Spec (CommRingCat.of k)
  -- notation
  set W := X.pointClosure w with hWdef
  set ι := X.pointClosureι w with hιdef
  set W' := Y.pointClosure (f.base w) with hW'def
  set ι' := Y.pointClosureι (f.base w) with hι'def
  have hYLN : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ S)
  have hLN' : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian ι'
  -- `g := ι ≫ f`, its scheme-theoretic image and the isomorphism to `W'`
  let g : W ⟶ Y := ι ≫ f
  have hgint : IsIntegral g.image := g.isIntegral_image
  have hgprop : IsProper g.toImage := by
    have : IsProper (g.toImage ≫ g.imageι) := by rw [g.toImage_imageι]; infer_instance
    exact IsProper.of_comp g.toImage g.imageι
  have hgen'' : g.imageι.base (genericPoint g.image) = f.base w := by
    rw [← g.toImage.base_genericPoint_of_isDominant]
    have h1 : g.imageι.base (g.toImage.base (genericPoint W)) =
        (g.toImage ≫ g.imageι).base (genericPoint W) := rfl
    rw [h1, g.toImage_imageι]
    have h2 : g.base (genericPoint W) = f.base (ι.base (genericPoint W)) := rfl
    rw [h2, hιdef, Scheme.pointClosureι_genericPoint]
  obtain ⟨θ, hθ⟩ := MiyaokaMori.PointClosureTransport.exists_iso_pointClosure_of_isClosedImmersion
    g.imageι (f.base w) hgen''
  let p' : W ⟶ W' := g.toImage ≫ θ.hom
  have hp'ι : p' ≫ ι' = g := by
    show (g.toImage ≫ θ.hom) ≫ ι' = g
    rw [Category.assoc, hθ, g.toImage_imageι]
  have hp'prop : IsProper p' := by
    have : IsProper (p' ≫ ι') := by rw [hp'ι]; infer_instance
    exact IsProper.of_comp p' ι'
  have hp'gen : p'.base (genericPoint W) = genericPoint W' := by
    apply ι'.isClosedEmbedding.injective
    have h1 : ι'.base (p'.base (genericPoint W)) = (p' ≫ ι').base (genericPoint W) := rfl
    rw [h1, hp'ι]
    have h2 : g.base (genericPoint W) = f.base (ι.base (genericPoint W)) := rfl
    rw [h2, hιdef, Scheme.pointClosureι_genericPoint, hι'def, Scheme.pointClosureι_genericPoint]
  -- `k`-structures
  letI : W.Over S := ⟨ι ≫ (X ↘ S)⟩
  letI : W'.Over S := ⟨ι' ≫ (Y ↘ S)⟩
  haveI : LocallyOfFiniteType (W ↘ S) := inferInstanceAs (LocallyOfFiniteType (ι ≫ (X ↘ S)))
  haveI : LocallyOfFiniteType (W' ↘ S) := inferInstanceAs (LocallyOfFiniteType (ι' ≫ (Y ↘ S)))
  haveI : p'.IsOver S := ⟨by
    show p' ≫ (ι' ≫ (Y ↘ S)) = ι ≫ (X ↘ S)
    rw [← Category.assoc, hp'ι]
    show (ι ≫ f) ≫ (Y ↘ S) = ι ≫ (X ↘ S)
    rw [Category.assoc, comp_over f S]⟩
  -- factorization of the pushforward
  have hcomp : AlgebraicGeometry.AlgebraicCycle.properPushforward f (AlgebraicGeometry.AlgebraicCycle.properPushforward ι
      (W.principalCycle r)) = AlgebraicGeometry.AlgebraicCycle.properPushforward ι'
        (AlgebraicGeometry.AlgebraicCycle.properPushforward p' (W.principalCycle r)) := by
    rw [AlgebraicCycle.properPushforward_comp, AlgebraicCycle.properPushforward_comp]
    exact properPushforward_congr' hp'ι.symm _
  -- dimensions
  have hdimW : topologicalKrullDim W = ((p + 1 : ℕ) : WithBot ℕ∞) :=
    Scheme.topologicalKrullDim_pointClosure w hw
  have hle : Order.height (f.base w) ≤ ((p + 1 : ℕ) : ℕ∞) := by
    rw [← hw]
    exact Scheme.height_apply_le_of_specializingMap f f.isClosedMap.specializingMap w
  rcases hle.lt_or_eq with hlt | heq
  · -- dimension drop: the pushforward is zero
    left
    have hne : Order.height (f.base w) ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨d', hd'⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hd'] at hlt
    have hd'lt : d' < p + 1 := by exact_mod_cast hlt
    have hdimW' : topologicalKrullDim W' = ((d' : ℕ) : WithBot ℕ∞) :=
      Scheme.topologicalKrullDim_pointClosure (f.base w) hd'.symm
    rw [hcomp, properPushforward_principalCycle_eq_zero_of_dimension_lt (k := k) p' hp'gen
      (p + 1) d' hdimW hdimW' hd'lt r]
    exact map_zero (AlgebraicCycle.properPushforwardHom ι')
  · -- no dimension drop: 02RT
    right
    have hdimW' : topologicalKrullDim W' = ((p + 1 : ℕ) : WithBot ℕ∞) :=
      Scheme.topologicalKrullDim_pointClosure (f.base w) heq
    have h02rt := properPushforward_principalCycle_of_locallyOfFiniteType (k := k) p' hp'gen
      (p + 1) hdimW hdimW' r
    letI := functionFieldAlgebra p' hp'gen
    refine ⟨heq, inferInstance, inferInstance, hLN',
      Units.map (Algebra.norm W'.functionField) r, ?_⟩
    rw [hcomp]
    exact congrArg (AlgebraicGeometry.AlgebraicCycle.properPushforward ι') h02rt

end AlgebraicGeometry

end
