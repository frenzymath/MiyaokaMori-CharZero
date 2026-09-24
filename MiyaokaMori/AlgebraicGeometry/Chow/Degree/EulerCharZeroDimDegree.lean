import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.GrothendieckVanishing
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyZeroEquiv

/-! # Euler characteristic of a zero-dimensional proper scheme is the degree of its fundamental cycle

The Euler characteristic of a zero-dimensional proper scheme equals the degree of its fundamental
cycle: for `dim X = 0`, `χ(X, O_X) = Σ_x length(O_{X,x})·[κ(x):k] = deg [X]_0`. This is the case
`d = 0` of the agreement between the `χ`-intersection number and the Chow degree.

Source: Lazarsfeld, Positivity in Algebraic Geometry I, §1.1.C, footnote 7 (the `d = 0` case of the
Snapper intersection number).

## Route

Let `p : X ⟶ Spec k` be the structure morphism and `A := Γ(X, O_X)`.

1. **X is an Artinian scheme.** `X.dimension = 0` and `X` proper over `k` give `topologicalKrullDim X ≤ 0`
   (`topologicalKrullDim_ne_top_of_isProperOver` rules out the `⊤` fallback of `X.dimension`), so `X` is locally
   Artinian (`IsLocallyArtinian.of_topologicalKrullDim_le_zero`), quasi-compact, hence `IsArtinianScheme X`:
   finite, discrete and affine (Mathlib instances).
2. **`A` is a finite `k`-algebra.** `p` is proper and `X`, `Spec k` are affine, so `p` is integral
   (`IsIntegralHom.iff_universallyClosed_and_isAffineHom`) and of finite type, hence finite
   (`IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`), and `p.appTop` is a finite ring map
   (`Scheme.Hom.finite_appTop`); these are Mathlib results.
3. **χ(X, O_X) = dim_k H⁰(X, O_X).** For `i ≥ 1`, `Hⁱ(X, O_X) = 0` by affine vanishing (Stacks 01XB,
   `sheafCohomology_subsingleton_of_isAffine`; `O_X` is quasi-coherent since it is locally free,
   `Scheme.Modules.unit_isLocallyFree`), so the `finsum` defining χ has support `⊆ {0}` — no fallback of
   `sheafEulerCharacteristic` is used. (The generic discipline `sheafEulerCharacteristic_eq_sum` needs
   `[IsCoherent O_X]`, which the library does not provide; Grothendieck vanishing 02UZ is **not** used.)
4. **H⁰(X, O_X) ≅ A `k`-linearly** (`sheafCohomologyZeroEquiv`, whose `Γ(X,⊤)`-linearity restricts along
   `k → A`); in particular `H⁰` is finite-dimensional, so `Module.finrank` is the true dimension.
5. **dim_k A = Σ_{q ∈ Spec A} dim_k A_q** (`IsArtinianRing.finrank_eq_sum_primeSpectrum`), and the points of
   `X` correspond bijectively to `Spec A` via `IsAffineOpen.primeIdealOf` (for `U = ⊤`), with
   `O_{X,x} ≅ A_{q(x)}` (`IsAffineOpen.isLocalization_stalk`).
6. **Local algebra.** For a local ring `R` finite over `k` with residue field `κ`:
   `dim_k R = length_R(R) · [κ : k]` (`Module.finrank_eq_length_toNat_mul_finrank_residueField`, from
   `IsLocalRing.length_restrictScalars` — Stacks 02M0 for a local `B`; `Module.length_eq_sum_inertiaDeg_mul_length_localization` is not needed).
7. **Degree side.** Every point is closed and a generic point (discrete space), so `X.fundamentalCycle 0 x`
   is the integer lift of `length(O_{X,x})`, and `p.residueDegree x = [κ(x) : k]`
   (`Scheme.Hom.residueFieldDegree_eq_residueDegree`); the `k`-structure on `κ(x)` used there
   (`AlgebraicGeometry.Intersection.pointBaseMap`) factors as `k → A → O_{X,x} → κ(x)`
   (`pointBaseMap_eq_structureRingHom_germ_residue`). Summing over the finitely many points gives the claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Local algebra of a finite-dimensional local algebra.** Let `R` be a local ring that is a finite
`k`-algebra (`k` a field) and let `κ` be a field with `k → R → κ` a scalar tower such that `R → κ` is
surjective with kernel the maximal ideal (so `κ` is the residue field of `R`). Then
`dim_k R = length_R(R) · [κ : k]`.

Proof: `length_k R = dim_k R` (`Module.length_eq_finrank`); `length_k R = length_R R · length_{κ_k} κ_R`
(`IsLocalRing.length_restrictScalars`, `k → R` is a local homomorphism since `k` is a field);
`length_{κ_k} κ_R = dim_{κ_k} κ_R = dim_k κ_R` because `k ≅ κ_k`; and `κ_R ≃ₐ[k] κ` by the first isomorphism
theorem. `length_R R` is finite because `R` is Artinian and Noetherian (finite over a field).
Edge case: `R` is nontrivial (local), so `[κ : k] ≥ 1` and nothing degenerates. -/
theorem Module.finrank_eq_length_toNat_mul_finrank_residueField (k R : Type u) [Field k]
    [CommRing R] [IsLocalRing R] [Algebra k R] [Module.Finite k R]
    (κ : Type u) [Field κ] [Algebra R κ] [Algebra k κ] [IsScalarTower k R κ]
    (hκ : Function.Surjective (algebraMap R κ))
    (hker : RingHom.ker (algebraMap R κ) = IsLocalRing.maximalIdeal R) :
    Module.finrank k R = (Module.length R R).toNat * Module.finrank k κ := by
  have hArt : IsArtinianRing R := isArtinian_of_tower k inferInstance
  have hNoe : IsNoetherianRing R := isNoetherian_of_tower k inferInstance
  have hfin : Module.length R R ≠ ⊤ := Module.length_ne_top
  have h1 : Module.length k R = Module.finrank k R := Module.length_eq_finrank k R
  have h2 : Module.length k R = Module.length R R *
      Module.length (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R) :=
    IsLocalRing.length_restrictScalars k R R
  have : Module.Finite (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R) :=
    Module.Finite.of_restrictScalars_finite k _ _
  have h3 : Module.length (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R) =
      Module.finrank (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R) :=
    Module.length_eq_finrank _ _
  have h4 : Module.finrank k (IsLocalRing.ResidueField k) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      ⟨(algebraMap k (IsLocalRing.ResidueField k)).injective, IsLocalRing.residue_surjective⟩
  have h5 : Module.finrank (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R) =
      Module.finrank k (IsLocalRing.ResidueField R) := by
    have := Module.finrank_mul_finrank k (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField R)
    rw [h4, one_mul] at this
    exact this
  let e : IsLocalRing.ResidueField R ≃ₐ[k] κ :=
    (Ideal.quotientEquivAlgOfEq k hker).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := IsScalarTower.toAlgHom k R κ) hκ)
  have h6 : Module.finrank k (IsLocalRing.ResidueField R) = Module.finrank k κ :=
    e.toLinearEquiv.finrank_eq
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.length R R = n := ⟨_, (ENat.natCast_toNat hfin).symm⟩
  rw [hn, ENat.toNat_natCast]
  have key : ((Module.finrank k R : ℕ) : ℕ∞) = ((n * Module.finrank k κ : ℕ) : ℕ∞) := by
    rw [← h1, h2, hn, h3, h5, h6, Nat.cast_mul]
  exact_mod_cast key

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

/-- The structure ring homomorphism `k → Γ(X, O_X)` of a `k`-scheme (the ring map through which
`sheafCohomology.moduleOver` restricts scalars). -/
abbrev Scheme.structureRingHom : CommRingCat.of k ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop

/-- The base map `k → κ(x)` of `AlgebraicGeometry.Intersection.pointBaseMap` factors as
`k → Γ(X, O_X) → O_{X,x} → κ(x)`. Proof: `Spec` is fully faithful (`Spec.preimage_map`), the structure
morphism is `X.toSpecΓ ≫ Spec.map (structure ring map)` (`Scheme.toSpecΓ_naturality`), and
`X.fromSpecStalk x ≫ X.toSpecΓ = Spec.map (germ)` (`Scheme.fromSpecStalk_toSpecΓ`). -/
theorem pointBaseMap_eq_structureRingHom_germ_residue (x : X) :
    AlgebraicGeometry.Intersection.pointBaseMap (X ↘ Spec (CommRingCat.of k)) x =
      X.structureRingHom ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  unfold AlgebraicGeometry.Intersection.pointBaseMap
  have hp : (X ↘ Spec (CommRingCat.of k)) = X.toSpecΓ ≫ Spec.map X.structureRingHom := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [hp, Scheme.fromSpecResidueField, Category.assoc, ← Category.assoc (X.fromSpecStalk x),
    Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← Spec.map_comp, Spec.preimage_map,
    Category.assoc]

/-- A proper `k`-scheme with `X.dimension = 0` has topological Krull dimension `≤ 0`
(`X.dimension` truncates `⊥` and `⊤` to `0`; `⊤` is excluded by properness, `⊥` means `X = ∅`). -/
theorem topologicalKrullDim_le_zero_of_dimension_eq_zero (hX : IsProperOver k X)
    (hd : X.dimension = 0) : topologicalKrullDim X ≤ 0 := by
  by_cases hb : topologicalKrullDim X = ⊥
  · rw [hb]; exact bot_le
  · rw [X.dimension_spec hb (topologicalKrullDim_ne_top_of_isProperOver X hX), hd]
    rfl

/-- In a discrete space every point is the generic point of an irreducible component: the irreducible
component of `x` is a subsingleton (two distinct points would be disjoint nonempty open subsets),
hence equals `{x} = closure {x}`. -/
theorem mem_genericPoints_of_discreteTopology [DiscreteTopology X] (x : X) :
    x ∈ genericPoints X := by
  show closure ({x} : Set X) ∈ irreducibleComponents X
  rw [closure_singleton]
  have hsub : irreducibleComponent x ⊆ {x} := by
    intro y hy
    obtain ⟨z, hz⟩ := (isIrreducible_irreducibleComponent (x := x)).2 {x} {y}
      (isOpen_discrete _) (isOpen_discrete _) ⟨x, mem_irreducibleComponent, rfl⟩ ⟨y, hy, rfl⟩
    have h1 : z = x := hz.2.1
    have h2 : z = y := hz.2.2
    rw [Set.mem_singleton_iff, ← h2, h1]
  have heq : irreducibleComponent x = {x} :=
    Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
  rw [← heq]
  exact irreducibleComponent_mem_irreducibleComponents x

end AlgebraicGeometry

open Classical AlgebraicGeometry in
/-- **χ(X, O_X) = deg [X]₀ for a zero-dimensional proper `k`-scheme** (the `d = 0`
case of the comparison between the Snapper intersection number and the Chow degree). The route is
described in the module docstring: `X` is a finite discrete affine scheme, `χ = dim_k Γ(X, O_X)` by affine
vanishing, and `dim_k Γ(X, O_X) = Σ_x length(O_{X,x})·[κ(x):k]` by the Artinian decomposition of
`Γ(X, O_X)` together with `Module.finrank_eq_length_toNat_mul_finrank_residueField`.
Edge cases: `X = ∅` gives `0 = 0` (both sides are empty sums); non-reduced points contribute their length. -/
theorem AlgebraicGeometry.sheafEulerCharacteristic_eq_degree_fundamentalCycle {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) [AlgebraicGeometry.IsLocallyNoetherian X] (hd : X.dimension = 0) :
    (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
        (SheafOfModules.unit X.ringCatSheaf) : ℤ)
      = AlgebraicGeometry.AlgebraicCycle.degree (k := k) (X.fundamentalCycle 0) := by
  set p := X ↘ Spec (CommRingCat.of k)
  set M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hprop : IsProper p := hX
  -- Step 1: X is an Artinian scheme: finite, discrete, affine.
  have : IsLocallyArtinian X :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero
      (topologicalKrullDim_le_zero_of_dimension_eq_zero X hX hd)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsArtinianScheme X := ⟨⟩
  have : Finite X := inferInstance
  have : DiscreteTopology X := inferInstance
  have : IsAffine X := inferInstance
  let _ : Fintype X := Fintype.ofFinite X
  -- Step 2: Γ(X, O_X) is a finite k-algebra (X → Spec k is finite: proper + affine).
  let _ : Algebra k Γ(X, ⊤) := (X.structureRingHom (k := k)).hom.toAlgebra
  have : IsFinite p :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType p).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩,
        inferInstance⟩
  have hφ : (X.structureRingHom (k := k)).hom.Finite := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Finite.comp p.finite_appTop
      (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have hfinA : Module.Finite k Γ(X, ⊤) := hφ
  -- Step 3: χ(X, O_X) = dim_k H⁰ (all Hⁱ, i ≥ 1, vanish: X is affine, O_X quasi-coherent).
  have hchi : sheafEulerCharacteristic (k := k) X M
      = (Module.finrank k (sheafCohomology X M 0) : ℤ) := by
    unfold sheafEulerCharacteristic
    rw [finsum_eq_single _ 0]
    · simp
    · intro i hi
      have := sheafCohomology_subsingleton_of_isAffine M i (Nat.pos_of_ne_zero hi)
      simp [Module.finrank_zero_of_subsingleton]
  -- Step 4: H⁰(X, O_X) ≅ Γ(X, O_X) k-linearly.
  have hH0 : Module.finrank k (sheafCohomology X M 0) = Module.finrank k Γ(X, ⊤) := by
    let e := sheafCohomologyZeroEquiv M
    let e' : sheafCohomology X M 0 ≃ₗ[k] Γ(X, ⊤) :=
      { toFun := e
        invFun := e.symm
        map_add' := e.map_add
        map_smul' := fun c x => e.map_smul ((X.structureRingHom (k := k)).hom c) x
        left_inv := e.left_inv
        right_inv := e.right_inv }
    exact e'.finrank_eq
  -- Step 5: dim_k Γ(X, O_X) = Σ_{q ∈ Spec Γ} dim_k Γ_q (Artinian ring).
  have : IsArtinianRing Γ(X, ⊤) := inferInstance
  let _ : Fintype (PrimeSpectrum Γ(X, ⊤)) := Fintype.ofFinite _
  have hsum := IsArtinianRing.finrank_eq_sum_primeSpectrum Γ(X, ⊤) k
  -- Step 6: points of X ↔ primes of Γ(X, O_X).
  let hU := isAffineOpen_top X
  have hψ : Function.Bijective (fun x : X => hU.primeIdealOf ⟨x, trivial⟩) := by
    have hb := hU.isoSpec.hom.homeomorph.bijective
    constructor
    · intro x y hxy
      exact congrArg Subtype.val (hb.1 (a₁ := ⟨x, trivial⟩) (a₂ := ⟨y, trivial⟩) hxy)
    · intro q
      obtain ⟨⟨x, _⟩, hx⟩ := hb.2 q
      exact ⟨x, hx⟩
  let ψ : X ≃ PrimeSpectrum Γ(X, ⊤) := Equiv.ofBijective _ hψ
  -- Step 7: per point, dim_k Γ_q = dim_k O_{X,x} = length(O_{X,x}) · [κ(x) : k].
  have hpt : ∀ x : X, Module.finrank k (Localization.AtPrime (ψ x).asIdeal)
      = (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat *
          AlgebraicGeometry.Intersection.residueFieldDegree p x := by
    intro x
    let _ : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf (U := ⊤) ⟨x, trivial⟩
    have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (ψ x).asIdeal :=
      hU.isLocalization_stalk ⟨x, trivial⟩
    let _ : Algebra k (X.presheaf.stalk x) :=
      ((algebraMap Γ(X, ⊤) (X.presheaf.stalk x)).comp (algebraMap k Γ(X, ⊤))).toAlgebra
    have : IsScalarTower k Γ(X, ⊤) (X.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let e : X.presheaf.stalk x ≃ₐ[Γ(X, ⊤)] Localization.AtPrime (ψ x).asIdeal :=
      IsLocalization.algEquiv (ψ x).asIdeal.primeCompl _ _
    let e' := e.restrictScalars k
    have h1 : Module.finrank k (Localization.AtPrime (ψ x).asIdeal)
        = Module.finrank k (X.presheaf.stalk x) := e'.toLinearEquiv.finrank_eq.symm
    have : Module.Finite k (Localization.AtPrime (ψ x).asIdeal) :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom k Γ(X, ⊤) _).toLinearMap
        (IsArtinianRing.localization_surjective (ψ x).asIdeal.primeCompl _)
    have : Module.Finite k (X.presheaf.stalk x) := Module.Finite.equiv e'.symm.toLinearEquiv
    let _ : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
    let _ : Algebra k (X.residueField x) :=
      (AlgebraicGeometry.Intersection.pointBaseMap p x).hom.toAlgebra
    have : IsScalarTower k (X.presheaf.stalk x) (X.residueField x) :=
      IsScalarTower.of_algebraMap_eq (fun c => by
        show (AlgebraicGeometry.Intersection.pointBaseMap p x).hom c =
          (X.residue x).hom ((X.presheaf.germ ⊤ x trivial).hom ((X.structureRingHom (k := k)).hom c))
        rw [pointBaseMap_eq_structureRingHom_germ_residue]
        rfl)
    have hsurj : Function.Surjective (algebraMap (X.presheaf.stalk x) (X.residueField x)) :=
      IsLocalRing.residue_surjective
    have hker : RingHom.ker (algebraMap (X.presheaf.stalk x) (X.residueField x)) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := IsLocalRing.ker_residue
    rw [h1, Module.finrank_eq_length_toNat_mul_finrank_residueField k (X.presheaf.stalk x)
      (X.residueField x) hsurj hker]
    rfl
  -- Step 8: the degree of the fundamental cycle, pointwise.
  have hdeg : AlgebraicCycle.degree (k := k) (X.fundamentalCycle 0) =
      ∑ x : X, (((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) *
        (AlgebraicGeometry.Intersection.residueFieldDegree p x : ℤ)) := by
    unfold AlgebraicCycle.degree
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Scheme.Hom.residueFieldDegree_eq_residueDegree p x]
    congr 1
    show (if AlgebraicGeometry.Intersection.pointClosureDimension X x = ((0 : ℕ) : WithBot ℕ∞)
        then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X x else 0) = _
    have h0 : AlgebraicGeometry.Intersection.pointClosureDimension X x = ((0 : ℕ) : WithBot ℕ∞) := by
      rw [AlgebraicGeometry.Intersection.pointClosureDimension_eq_zero_of_isClosed x (isClosed_discrete _)]
      simp
    rw [if_pos h0]
    have h := AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_toNat X x
    rw [AlgebraicGeometry.Intersection.fundamentalMultiplicity_of_generic X x
      (mem_genericPoints_of_discreteTopology X x)] at h
    rw [← Int.toNat_of_nonneg (AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_nonneg X x)]
    congr 1
    unfold AlgebraicGeometry.Intersection.stalkLength at h
    rw [← h, ENat.toNat_natCast]
  -- Step 9: assemble.
  rw [hchi, hH0, hsum, hdeg,
    ← Fintype.sum_equiv ψ (fun x => Module.finrank k (Localization.AtPrime (ψ x).asIdeal))
      (fun q => Module.finrank k (Localization.AtPrime q.asIdeal)) (fun _ => rfl)]
  push_cast
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hpt x]
  push_cast
  ring

end
