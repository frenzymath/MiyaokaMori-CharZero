import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionCurve
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveSpaceProper
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPowerMapDegree
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.InducedByPowerMapIsOver
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.WeightedProjOneTwistTopDegree
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjSpaceDimension
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveSpaceIsIntegral
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedToOrdinaryProj
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure

/-! # The top self-intersection of `O(m)` on a weighted projective space

On `P(a_0,…,a_N)` the top self-intersection of `O(m)` times `∏ a_i` equals `m^N`; when all `a_i ∣ m` it is
a positive integer (the fiber degree `v_k` of Proposition 2.4 of the paper).

## Route

The main theorem `weightedProjectiveSpace_topSelfIntersection` is assembled as follows. Let
`φ : P^N = P(1,…,1) → P(w)` be the power map (`finite_surjective_toWeightedProj`);

* `weightedPowerMap_degree_twist`: deg φ = ∏ w_i, φ^*O_{P(w)}(m) ≅ O_{P^N}(m) (w_i ∣ m); 
* the projection formula iterated `N` times (`chowPushforward_capPow_of_pullbackIso` of
  `TopSelfIntersectionIsoInvariant`, with `L₀ = φ^*L`);
* `φ_*[P^N] = (deg φ)[P(w)]` (`properPushforward_fundamentalCycle_of_surjective`, a direct computation at
  the level of cycles);
* the degree of zero-dimensional classes is compatible with the pushforward (`degreeOver_chowPushforward`);
* `(O_{P^N}(m)^N) = m^N` (`weightedProjectiveSpace_one_topSelfIntersection`).

The inputs proved in their own modules: `weightedProjectiveSpace.isIntegral` (`P(w)` is integral),
`InducedByPowerMap.comp_over` (`φ` is a `k`-morphism), `weightedProjectiveSpace_one_topSelfIntersection`
(the computation on `P^N`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## Auxiliary lemmas -/

/-- The height of the generic point of an integral scheme is its dimension (when finite); the version of
`height_genericPoint_of_dimension` without `0 < d`. -/
theorem AlgebraicGeometry.height_genericPoint_eq_dimension {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (hX : topologicalKrullDim X ≠ ⊤) :
    Order.height (genericPoint X) = (X.dimension : ℕ∞) := by
  have hk : Order.krullDim X = topologicalKrullDim X :=
    (Order.krullDim_eq_of_orderIso
      (@irreducibleSetEquivPoints X _ _ _ :
        TopologicalSpace.IrreducibleCloseds X ≃o X)).symm
  have h1 : ((Order.height (⊤ : X) : ℕ∞) : WithBot ℕ∞) = Order.krullDim X :=
    Order.height_top_eq_krullDim
  rw [hk, X.dimension_spec MiyaokaMori.TopSelfIntersectionCurve.topologicalKrullDim_ne_bot hX] at h1
  exact WithBot.coe_injective h1

/-- A surjection sends the generic point to the generic point. -/
theorem AlgebraicGeometry.Scheme.Hom.base_genericPoint_of_surjective {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y)
    (hf : Function.Surjective f.base) : f.base (genericPoint X) = genericPoint Y := by
  have h1 : IsGenericPoint (f.base (genericPoint X)) (closure (f.base '' Set.univ)) :=
    (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, hf.range_eq, closure_univ] at h1
  exact h1.eq (genericPoint_spec Y)

/-- **The pushforward formula at the level of cycles** `f_*[X] = [K(X) : K(Y)]·[Y]`: `X`, `Y` integral of the
same finite dimension, `f` proper and surjective (Fulton 1.4: `f_*[V] = deg(V/W)[W]`, `W = f(V)`,
`dim V = dim W`). Proof: `[X]` is the single-point cycle at the generic point `η_X`
(`fundamentalCycle_of_isIntegral`); the coefficient of the pushforward at `y` is
`∑_{x ∈ f⁻¹(y)} [X](x)·mapCoeff(x)`, and only `x = η_X` contributes; `f` surjective ⇒ `f(η_X) = η_Y`;
`height η_X = dim X = dim Y = height η_Y`, so `mapCoeff(η_X) = residueDegree η_X = functionFieldDegree f`. -/
theorem AlgebraicGeometry.properPushforward_fundamentalCycle_of_surjective
    {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y]
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (hf : Function.Surjective f.base)
    (hX : topologicalKrullDim X ≠ ⊤) (hY : topologicalKrullDim Y ≠ ⊤)
    (hdim : X.dimension = Y.dimension) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f (X.fundamentalCycle X.dimension)
      = ((functionFieldDegree f : ℕ) : ℤ) • Y.fundamentalCycle Y.dimension := by
  classical
  have hfX := congrFun (X.fundamentalCycle_of_isIntegral hX)
  have hfY := congrFun (Y.fundamentalCycle_of_isIntegral hY)
  have hgen : f.base (genericPoint X) = genericPoint Y :=
    AlgebraicGeometry.Scheme.Hom.base_genericPoint_of_surjective f hf
  have hh : Order.height (genericPoint X) = Order.height (f.base (genericPoint X)) := by
    rw [hgen, AlgebraicGeometry.height_genericPoint_eq_dimension hX,
      AlgebraicGeometry.height_genericPoint_eq_dimension hY, hdim]
  ext y
  change ∑ᶠ x ∈ f.base ⁻¹' {y}, X.fundamentalCycle X.dimension x *
      ((AlgebraicCycle.mapCoeff f (Order.height (α := X)) (Order.height (α := Y)) x : ℕ) : ℤ) = _
  rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul, hfY y, finsum_mem_def,
    finsum_eq_single _ (genericPoint X)]
  · rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hgen, hfX, if_true, one_mul]
    unfold AlgebraicCycle.mapCoeff
    rw [if_pos hh]
    by_cases hy : genericPoint Y = y
    · rw [if_pos hy, if_pos hy.symm, mul_one]
      rfl
    · rw [if_neg hy, if_neg (Ne.symm hy), mul_zero]
  · intro x hx
    rw [Set.indicator_apply]
    simp only [hfX x, if_neg hx, zero_mul, ite_self]

/-- In the Chow group: `f_*[X] = [K(X) : K(Y)]·[Y]`. -/
theorem AlgebraicGeometry.chowPushforward_fundamentalChowClass {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper f]
    (hf : Function.Surjective f.base)
    (hX : topologicalKrullDim X ≠ ⊤) (hY : topologicalKrullDim Y ≠ ⊤)
    {d : ℕ} (hdX : X.dimension = d) (hdY : Y.dimension = d) :
    AlgebraicGeometry.chowPushforward f d (X.fundamentalChowClass d)
      = ((functionFieldDegree f : ℕ) : ℤ) • Y.fundamentalChowClass d := by
  have hcyc : AlgebraicGeometry.AlgebraicCycle.properPushforward f (X.fundamentalCycle d)
      = ((functionFieldDegree f : ℕ) : ℤ) • Y.fundamentalCycle d := by
    subst hdX
    have h := AlgebraicGeometry.properPushforward_fundamentalCycle_of_surjective f hf hX hY hdY.symm
    rw [hdY] at h
    exact h
  have hdesc : AlgebraicGeometry.PushforwardDescends f d :=
    AlgebraicGeometry.AlgebraicCycle.properPushforward_rationallyEquivalent (k := k) f d
  unfold AlgebraicGeometry.Scheme.fundamentalChowClass
  rw [AlgebraicGeometry.chowPushforward_mk f d hdesc, ← map_zsmul]
  congr 1
  apply Subtype.ext
  exact hcyc

/-- The `cast` along the dimension index commutes with the pushforward. -/
theorem AlgebraicGeometry.chowPushforward_cast {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] {d d' : ℕ} (h : d = d')
    (α : AlgebraicGeometry.ChowGroup X d) :
    AlgebraicGeometry.chowPushforward f d' (cast (congrArg (AlgebraicGeometry.ChowGroup X) h) α)
      = cast (congrArg (AlgebraicGeometry.ChowGroup Y) h) (AlgebraicGeometry.chowPushforward f d α) := by
  subst h
  rfl

/-- The `cast` along the dimension index commutes with integer multiples. -/
theorem AlgebraicGeometry.ChowGroup.cast_zsmul {X : AlgebraicGeometry.Scheme.{u}} {d d' : ℕ} (h : d = d')
    (n : ℤ) (α : AlgebraicGeometry.ChowGroup X d) :
    cast (congrArg (AlgebraicGeometry.ChowGroup X) h) (n • α)
      = n • cast (congrArg (AlgebraicGeometry.ChowGroup X) h) α := by
  subst h
  rfl

/-- The dimension of `P(w)` (`ℕ` version): `dim P(w) = |σ| − 1`. -/
theorem weightedProjectiveSpace_dimension_nat (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    [Nonempty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    (weightedProjectiveSpace k w hw).dimension = Fintype.card σ - 1 := by
  unfold AlgebraicGeometry.Scheme.dimension
  rw [weightedProjectiveSpace_dimension k w hw]
  exact ENat.toNat_natCast _

/-- `P(w)` is finite-dimensional. -/
theorem weightedProjectiveSpace_topologicalKrullDim_ne_top (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [Nonempty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    topologicalKrullDim (weightedProjectiveSpace k w hw) ≠ ⊤ := by
  rw [weightedProjectiveSpace_dimension k w hw]
  intro h
  exact ENat.natCast_ne_top _ (WithBot.coe_injective h)

/-! ## Main theorem -/

/-- **The top self-intersection of `O(m)` on `P(w)`**: `(O(m)^N) · ∏ w_i = m^N` when all `w_i ∣ m` and some
`w_i = 1`. -/
theorem weightedProjectiveSpace_topSelfIntersection (k : Type u) [Field k] [IsAlgClosed k]
    {σ : Type u} [Fintype σ] [Nonempty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h1 : ∃ i, w i = 1)
    (m : ℕ) (hm : ∀ i, w i ∣ m) (hP : IsProperOver k (weightedProjectiveSpace k w hw))
    [(weightedProjTwist k w hw (m : ℤ)).IsLineBundle] :
    AlgebraicGeometry.topSelfIntersection (weightedProjectiveSpace k w hw) hP
        (weightedProjTwist k w hw (m : ℤ)) * (∏ i, (w i : ℤ))
      = (m : ℤ) ^ (Fintype.card σ - 1) := by
  classical
  -- notation
  set N := Fintype.card σ - 1 with hN
  set Pw := weightedProjectiveSpace k w hw with hPw
  set P1 := weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos) with hP1def
  set L := weightedProjTwist k w hw (m : ℤ) with hL
  -- the power map `φ : P^N → P(w)`
  obtain ⟨g, hfin, hsurj, hind⟩ := finite_surjective_toWeightedProj k w hw
  have : AlgebraicGeometry.IsFinite g := hfin
  have hint1 : AlgebraicGeometry.IsIntegral P1 :=
    weightedProjectiveSpace.isIntegral k (fun _ : σ => 1) (fun _ => Nat.one_pos)
  have hintw : AlgebraicGeometry.IsIntegral Pw := weightedProjectiveSpace.isIntegral k w hw
  obtain ⟨hdeg, hpull⟩ := weightedPowerMap_degree_twist k w hw h1 g hind
  obtain ⟨e⟩ := hpull m hm
  have : g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨InducedByPowerMap.comp_over k w hw g hind⟩
  have hP1 : IsProperOver k P1 := inferInstance
  have : (weightedProjTwist k (fun _ : σ => 1) (fun _ => Nat.one_pos) (m : ℤ)).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.of_iso e
  have : AlgebraicGeometry.IsLocallyNoetherian P1 :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (P1 ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsLocallyNoetherian Pw :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (Pw ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  -- dimensions
  have hdimw : Pw.dimension = N := weightedProjectiveSpace_dimension_nat k w hw
  have hdim1 : P1.dimension = N :=
    weightedProjectiveSpace_dimension_nat k (fun _ : σ => 1) (fun _ => Nat.one_pos)
  have hkw : topologicalKrullDim Pw ≠ ⊤ := weightedProjectiveSpace_topologicalKrullDim_ne_top k w hw
  have hk1 : topologicalKrullDim P1 ≠ ⊤ :=
    weightedProjectiveSpace_topologicalKrullDim_ne_top k (fun _ : σ => 1) (fun _ => Nat.one_pos)
  -- key identity: `(φ^*L)^N = deg φ · (L^N)`
  have key : AlgebraicGeometry.topSelfIntersection P1 hP1
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L)
      = ((functionFieldDegree g : ℕ) : ℤ) * AlgebraicGeometry.topSelfIntersection Pw hP L := by
    rw [MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_of_dimension hP1 _ hdim1,
      MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_of_dimension hP _ hdimw,
      ← MiyaokaMori.ChowDegreeRatPushforward.degreeOver_chowPushforward hP1 hP g,
      AlgebraicGeometry.chowPushforward_capPow_of_pullbackIso (k := k) g L _ ⟨Iso.refl _⟩ N 0,
      AlgebraicGeometry.chowPushforward_cast g (zero_add N).symm,
      AlgebraicGeometry.chowPushforward_fundamentalChowClass (k := k) g hsurj hk1 hkw hdim1 hdimw,
      AlgebraicGeometry.ChowGroup.cast_zsmul (zero_add N).symm, map_zsmul, map_zsmul, zsmul_eq_mul,
      Int.cast_id]
  -- the left side is `m^N`
  have hleft : AlgebraicGeometry.topSelfIntersection P1 hP1
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L) = (m : ℤ) ^ N := by
    rw [AlgebraicGeometry.topSelfIntersection_congr P1 hP1 _ _ e]
    exact weightedProjectiveSpace_one_topSelfIntersection k m hP1
  have hdeg' : ((functionFieldDegree g : ℕ) : ℤ) = ∏ i, (w i : ℤ) := by
    rw [hdeg]; push_cast; rfl
  rw [← hleft, key, hdeg', mul_comm]

end
