import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.AlgebraicCycles
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Degree of an actual zero cycle

For a proper locally finite type scheme over a field, this module defines the raw degree of a
zero-dimensional algebraic cycle as the finite sum of its integer coefficients weighted by the
actual residue-field degrees. The residue degree is used only after a proof that the corresponding
extension is finite; `Module.finrank` at an infinite extension is never a geometric multiplicity.
The descent through rational equivalence and the Cartier actions are treated in later modules.

Sources: Stacks Project, Chow, Definition `degree-zero-cycle` and Lemma
`spell-out-degree-zero-cycle` (Tags 0AZ1 and 0AZ2).

The library has **one** 0-cycle degree primitive, `AlgebraicGeometry.AlgebraicCycle.degree`
(`∑ᶠ x, Z x · [κ(x):k]` with Mathlib's `Scheme.Hom.residueDegree`, on any `AlgebraicCycle X ℤ` of a
scheme `X` over `Spec k`). `rawZeroCycleDegree f α` is an `abbrev` of it — the structure morphism `f`
is passed explicitly, the `X.Over (Spec K)` instance is `⟨f⟩`. `residueFieldDegree_eq_residueDegree`
identifies the residue-field degree used here with Mathlib's, so the finite-sum spellings
`rawZeroCycleDegree_eq_sum*` are available.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical BigOperators

universe u

/-- The degree of an algebraic cycle `Z` on a scheme `X` over a field `k` (structure morphism from the `X.Over (Spec k)`
instance): `deg Z = ∑ₓ Z(x) · [κ(x) : k]`, where `[κ(x) : k]` is Mathlib's `Scheme.Hom.residueDegree` (`Module.finrank`,
which is `0` at a point whose residue field is infinite over `k`, so only the closed points of a scheme of finite type
contribute). Stacks 0AZ1 (Definition `degree-zero-cycle`), Fulton Def. 1.4, for the integer-valued version on any
proper `k`-scheme. This is the **only** 0-cycle degree primitive of the library:
`rawZeroCycleDegree` below is an `abbrev` of it,
`ChowGroup.degreeOver` (`ZeroCycleDegreeScheme.lean`) is its descent to `A_0(X)`, and
`CartierDivisor.degree`, `ChowGroupRat.degree`, `topSelfIntersection` are defined through it. -/
noncomputable def AlgebraicGeometry.AlgebraicCycle.degree {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : AlgebraicGeometry.AlgebraicCycle X ℤ) : ℤ :=
  ∑ᶠ x : X, Z x * ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).residueDegree x : ℤ)

theorem AlgebraicGeometry.AlgebraicCycle.degree_zero {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    AlgebraicGeometry.AlgebraicCycle.degree (k := k) (0 : AlgebraicGeometry.AlgebraicCycle X ℤ) = 0 := by
  unfold AlgebraicGeometry.AlgebraicCycle.degree
  simp

theorem AlgebraicGeometry.AlgebraicCycle.degree_neg {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (a : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.degree (k := k) (-a) =
      -AlgebraicGeometry.AlgebraicCycle.degree (k := k) a := by
  unfold AlgebraicGeometry.AlgebraicCycle.degree
  rw [show (fun x : X => (-a) x *
      ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).residueDegree x : ℤ)) =
      (fun x : X => -(a x * ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).residueDegree x : ℤ))) by
      funext x; simp]
  rw [finsum_neg_distrib]

namespace AlgebraicGeometry.Intersection

/-- A zero-dimensional scheme point is closed: its irreducible closure has no nontrivial
specialization. This is proved from the actual Krull dimension of that closure. -/
theorem isClosed_singleton_of_pointClosureDimension_zero {X : Scheme.{u}} (x : X)
    (hx : pointClosureDimension X x = 0) : IsClosed ({x} : Set X) := by
  have hx' : topologicalKrullDim (closure ({x} : Set X)) = 0 :=
    (pointClosureDimension_eq_topologicalKrullDim_closure X x).symm.trans hx
  let Y := closure ({x} : Set X)
  have hY : IsIrreducible Y := isIrreducible_singleton.closure
  let : IrreducibleSpace Y := isIrreducible_iff_irreducibleSpace.mp hY
  let topY : IrreducibleCloseds Y :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  have hmax : ∀ Z : IrreducibleCloseds Y, IsMax Z :=
    Order.krullDim_nonpos_iff_forall_isMax.mp hx'.le
  have heq (y : Y) : closure ({y} : Set Y) = Set.univ := by
    let Z : IrreducibleCloseds Y :=
      ⟨closure ({y} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩
    exact Set.Subset.antisymm (Set.subset_univ _) (hmax Z (show Z ≤ topY from Set.subset_univ _))
  have hsub : Subsingleton Y := ⟨fun y z ↦
    (show IsGenericPoint y Set.univ from heq y ▸ isGenericPoint_closure).eq
      (show IsGenericPoint z Set.univ from heq z ▸ isGenericPoint_closure)⟩
  have hcl : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact congrArg Subtype.val (hsub.elim ⟨y, hy⟩ ⟨x, subset_closure (Set.mem_singleton x)⟩)
    · exact subset_closure
  exact closure_eq_iff_isClosed.mp hcl

/-- A closed point has zero-dimensional closure. -/
theorem pointClosureDimension_eq_zero_of_isClosed {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) : pointClosureDimension X x = 0 := by
  rw [pointClosureDimension_eq_topologicalKrullDim_closure, hx.closure_eq]
  let : Nonempty ({x} : Set X) := ⟨⟨x, rfl⟩⟩
  let : IrreducibleSpace ({x} : Set X) :=
    isIrreducible_iff_irreducibleSpace.mp isIrreducible_singleton
  let : Nonempty (IrreducibleCloseds ({x} : Set X)) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

/-- An actual closed point, with any integer multiplicity, is an actual zero cycle. -/
def closedPointZeroCycle {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    (n : ℤ) : DimensionCycle X 0 :=
  ⟨Function.locallyFinsuppWithin.single x n, isDimensionCycle_of_pointClosureDimension <| by
    intro y hy
    by_cases hxy : y = x
    · subst y
      exact pointClosureDimension_eq_zero_of_isClosed x hx
    · exact (hy (by simp [Function.locallyFinsuppWithin.single_apply, hxy])).elim⟩

/-- The actual map from the base field to a point's residue field. -/
def pointBaseMap {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    CommRingCat.of K ⟶ X.residueField x :=
  Spec.preimage (X.fromSpecResidueField x ≫ f)

/-- A closed point of a locally finite type scheme has a finite residue-field extension. -/
theorem pointBaseMap_finite {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) : (pointBaseMap f x).hom.Finite := by
  have hi : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  let : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [← IsFinite.SpecMap_iff, pointBaseMap, Spec.map_preimage]
  infer_instance

/-- The finrank of the actual residue-field extension.

Finiteness and positivity at every point contributing to a zero cycle are proved below; this
definition alone does not assert finiteness. -/
def residueFieldDegree {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (x : X) : ℕ := by
  letI : Algebra K (X.residueField x) := (pointBaseMap f x).hom.toAlgebra
  exact Module.finrank K (X.residueField x)

end AlgebraicGeometry.Intersection

open AlgebraicGeometry.Intersection in
/-- The residue-field degree `residueFieldDegree p x = finrank_k κ(x)` (algebra structure through
`pointBaseMap p x`) is Mathlib's `p.residueDegree x = finrank_{κ(p x)} κ(x)`. Proof: `pointBaseMap p x` factors as
`g ≫ p.residueFieldMap x` with `g : k ⟶ κ(p x)` the base map of `Spec k` at the point `p x` (both sides have
`Spec.map _ = X.fromSpecResidueField x ≫ p`, by `Spec.map_preimage` and
`Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`); `g` is bijective because `κ(p x) ≅ k` for the unique
point of `Spec k` (`Spec.residueFieldIso`, and `k → (⊥).ResidueField` is bijective); so the two `finrank`s agree by
`Algebra.finrank_eq_of_equiv_equiv`. -/
theorem AlgebraicGeometry.Scheme.Hom.residueFieldDegree_eq_residueDegree {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    residueFieldDegree p x = p.residueDegree x := by
  let g : CommRingCat.of k ⟶ (Spec (CommRingCat.of k)).residueField (p x) :=
    Spec.preimage ((Spec (CommRingCat.of k)).fromSpecResidueField (p x))
  have hcomp : pointBaseMap p x = g ≫ p.residueFieldMap x := by
    apply Spec.map_injective
    rw [pointBaseMap, Spec.map_preimage, Spec.map_comp, Spec.map_preimage,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hg : Function.Bijective g.hom := by
    let : (p x).asIdeal.IsPrime := (p x).isPrime
    have hgeq : g = CommRingCat.ofHom (algebraMap k (p x).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (CommRingCat.of k) (p x)).inv := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp,
        Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    have hpbot : (p x).asIdeal = (⊥ : Ideal k) := Ideal.eq_bot_of_prime (p x).asIdeal
    let : (p x).asIdeal.IsMaximal := by rw [hpbot]; exact Ideal.bot_isMaximal
    have hsurj : Function.Surjective (algebraMap k (p x).asIdeal.ResidueField) :=
      Ideal.algebraMap_residueField_surjective (p x).asIdeal
    have hinj : Function.Injective (algebraMap k (p x).asIdeal.ResidueField) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField, hpbot]
    have hiso : Function.Bijective
        (Scheme.Spec.residueFieldIso (CommRingCat.of k) (p x)).inv.hom :=
      ConcreteCategory.bijective_of_isIso _
    rw [hgeq]
    exact hiso.comp ⟨hinj, hsurj⟩
  unfold residueFieldDegree Scheme.Hom.residueDegree
  let : Algebra k (X.residueField x) := (pointBaseMap p x).hom.toAlgebra
  let : Algebra ((Spec (CommRingCat.of k)).residueField (p x)) (X.residueField x) :=
    (p.residueFieldMap x).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective g.hom hg) (RingEquiv.refl _) ?_
  ext t
  change (p.residueFieldMap x).hom (g.hom t) = (pointBaseMap p x).hom t
  rw [hcomp]
  rfl

namespace AlgebraicGeometry.Intersection

theorem residueFieldDegree_eq_one {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) : residueFieldDegree f x = 1 := by
  letI : Algebra K (X.residueField x) := (pointBaseMap f x).hom.toAlgebra
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  exact ConcreteCategory.bijective_of_isIso (residueFieldIsoBase f x hx).inv

/-- Every point in the support of a zero cycle has a genuinely finite residue extension. -/
theorem zeroCycle_pointBaseMap_finite {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (α : DimensionCycle X 0) (x : X) (hx : α.1 x ≠ 0) :
    (pointBaseMap f x).hom.Finite :=
  pointBaseMap_finite f x (isClosed_singleton_of_pointClosureDimension_zero x
      (IsDimensionCycle.pointClosureDimension_eq α.2 x hx))

/-- Each residue-field weight on the support is positive; no infinite-degree default is used. -/
theorem zeroCycle_residueFieldDegree_pos {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (α : DimensionCycle X 0) (x : X) (hx : α.1 x ≠ 0) : 0 < residueFieldDegree f x := by
  letI : Algebra K (X.residueField x) := (pointBaseMap f x).hom.toAlgebra
  letI : Module.Finite K (X.residueField x) := zeroCycle_pointBaseMap_finite f α x hx
  exact Module.finrank_pos

theorem cycle_finiteSupport {X : Scheme.{u}} [CompactSpace X] (α : AlgebraicCycle X ℤ) :
    (Function.support α).Finite := by
  simpa using α.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ

/-- Properness over a field supplies compactness, so every cycle has finite support. -/
theorem properCycle_finiteSupport {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] (α : AlgebraicCycle X ℤ) :
    (Function.support α).Finite := by
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact cycle_finiteSupport α

/-- A proper scheme over a field is Noetherian. -/
theorem properFieldScheme_isNoetherian {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] : IsNoetherian X := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

end AlgebraicGeometry.Intersection

open AlgebraicGeometry.Intersection in
/-- Additivity of the degree; `X` proper over `k` gives the finite supports (`properCycle_finiteSupport`). -/
theorem AlgebraicGeometry.AlgebraicCycle.degree_add {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsProper (X ↘ Spec (CommRingCat.of k))]
    (a b : AlgebraicCycle X ℤ) :
    AlgebraicCycle.degree (k := k) (a + b) =
      AlgebraicCycle.degree (k := k) a + AlgebraicCycle.degree (k := k) b := by
  have ha0 : (Function.support a).Finite := properCycle_finiteSupport (X ↘ Spec (CommRingCat.of k)) a
  have hb0 : (Function.support b).Finite := properCycle_finiteSupport (X ↘ Spec (CommRingCat.of k)) b
  unfold AlgebraicCycle.degree
  rw [show (fun x : X => (a + b) x * ((X ↘ Spec (CommRingCat.of k)).residueDegree x : ℤ)) =
      (fun x : X => a x * ((X ↘ Spec (CommRingCat.of k)).residueDegree x : ℤ) +
        b x * ((X ↘ Spec (CommRingCat.of k)).residueDegree x : ℤ)) by
      funext x; simp [add_mul]]
  exact finsum_add_distrib (Function.HasFiniteSupport.mul_left ha0 _)
    (Function.HasFiniteSupport.mul_left hb0 _)

namespace AlgebraicGeometry.Intersection

/-- The degree of a 0-cycle `α` on `X` proper over `Spec K` (structure morphism `f` explicit): **an
`abbrev` of the one primitive** `AlgebraicCycle.degree`, read with the `X.Over (Spec K)` instance `⟨f⟩`. When `X`
already carries an `Over` instance and `f = X ↘ Spec K`, `rawZeroCycleDegree (X ↘ Spec K) α` and
`AlgebraicCycle.degree α.1` are definitionally equal (structure eta for `OverClass`), so `change`/`rfl` cross them.
`[IsProper f]` is not needed for the sum (`finsum`) but is kept so that every existing call site keeps its shape;
`rawZeroCycleDegree_eq_sum` restores the finite-sum spelling with `residueFieldDegree`. -/
abbrev rawZeroCycleDegree {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (α : DimensionCycle X 0) : ℤ :=
  @AlgebraicCycle.degree K _ X ⟨f⟩ α.1

/-- The raw degree may be computed over a finite set proven to contain the cycle support. -/
theorem rawZeroCycleDegree_eq_sum_on {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] (α : DimensionCycle X 0)
    (s : Finset X) (hs : ∀ x, x ∉ s → α.1 x = 0) :
    rawZeroCycleDegree f α = ∑ x ∈ s, α.1 x * (residueFieldDegree f x : ℤ) := by
  change (∑ᶠ x : X, α.1 x * (f.residueDegree x : ℤ)) = _
  rw [finsum_eq_sum_of_support_subset _ (s := s)]
  · exact Finset.sum_congr rfl fun x _ ↦ by
      rw [Scheme.Hom.residueFieldDegree_eq_residueDegree]
  · intro x hx
    by_contra hn
    exact hx (by simp [hs x hn])

theorem rawZeroCycleDegree_eq_sum {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (α : DimensionCycle X 0) :
    rawZeroCycleDegree f α =
      ∑ x ∈ (properCycle_finiteSupport f α.1).toFinset,
        α.1 x * (residueFieldDegree f x : ℤ) :=
  rawZeroCycleDegree_eq_sum_on f α _ fun x hx ↦ by
    by_contra hn
    exact hx ((properCycle_finiteSupport f α.1).mem_toFinset.mpr hn)

/-- Over an algebraically closed base each actual residue degree is one. -/
theorem rawZeroCycleDegree_eq_sum_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (α : DimensionCycle X 0) (s : Finset X) (hs : ∀ x, x ∉ s → α.1 x = 0) :
    rawZeroCycleDegree f α = ∑ x ∈ s, α.1 x := by
  rw [rawZeroCycleDegree_eq_sum_on f α s hs]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : α.1 x = 0
  · simp [hx]
  · rw [residueFieldDegree_eq_one f x
      (isClosed_singleton_of_pointClosureDimension_zero x
      (IsDimensionCycle.pointClosureDimension_eq α.2 x hx))]
    simp

/-- The generator formula retains the integer multiplicity and residue extension degree. -/
theorem rawZeroCycleDegree_closedPointZeroCycle {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (x : X) (hx : IsClosed ({x} : Set X)) (n : ℤ) :
    rawZeroCycleDegree f (closedPointZeroCycle x hx n) = n * (residueFieldDegree f x : ℤ) := by
  rw [rawZeroCycleDegree_eq_sum_on f (closedPointZeroCycle x hx n) {x} (by
    intro y hy
    have hxy : y ≠ x := by simpa using hy
    simp [closedPointZeroCycle, Function.locallyFinsuppWithin.single_apply, hxy])]
  simp [closedPointZeroCycle]

end AlgebraicGeometry.Intersection
