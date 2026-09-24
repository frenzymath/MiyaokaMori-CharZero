import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.NormalizationAffineIntegralClosure
import MiyaokaMori.RingTheory.Stacks035b

/-! # Finiteness of the relative normalization of locally algebraic schemes (Stacks 0BXS)

Stacks 0BXS: for a quasi-compact morphism `f : Y → X` of locally algebraic `k`-schemes with `Y`
reduced, the normalization `X' → X` of `X` in `Y` is a finite morphism (locally algebraic schemes
are Nagata). Via Stacks 035B (schemes locally of finite type over a field are Nagata) and 035S (over
a Nagata scheme, the relative normalization of a quasi-compact, quasi-separated, locally finite
type morphism with reduced source is finite).

## Proof structure

1. `integralClosure_sections_preimage_finite_of_locallyOfFiniteType` (the affine core of 035S): for
   an affine open `U` of `X`, write `A = Γ(X, U)` and `C = Γ(Y, f⁻¹U)` (`A → C` is `f.app U`).
   - `A` is of finite type over `k` (`finiteType_appLE` for the structure morphism `X → Spec k` and
     `⊤ ≥ U`), hence Noetherian (`Algebra.FiniteType.isNoetherianRing`).
   - `f` quasi-compact gives `f⁻¹U` quasi-compact, so `f⁻¹U = ⋃_{V∈s} V` for a finite set `s` of
     affine opens (`isCompact_iff_finite_and_eq_biUnion_affineOpens`).
   - For each `V ∈ s`, `B_V = Γ(Y, V)` is a finite type `A`-algebra via `f.appLE U V` (`f` locally
     of finite type) and reduced (`Y` reduced); by Stacks 035B (03GH + 0335: finite type algebras over
     a field are Nagata, and the integral closure of a Nagata ring in a reduced finite type algebra
     is finite), `integralClosure A B_V` is a finite `A`-module.
   - The restriction maps `C → B_V` are `A`-algebra maps sending integral elements to integral
     elements, giving an `A`-linear map `integralClosure A C → ∏_{V∈s} integralClosure A B_V`, which
     is injective by sheaf separatedness (`TopCat.Sheaf.eq_of_locally_eq'`, `s` covers `f⁻¹U`).
   - A finite product of finite modules is finite (`Module.Finite.pi`), and a submodule of a finite
     module over the Noetherian ring `A` is finite (`Module.Finite.of_injective`).
2. `normalization_isFinite_of_locallyOfFiniteType`: `bridge_isFinite_fromNormalization` (finiteness
   is affine-local on the target, and the section ring of `fromNormalization` over `U` is
   `integralClosure A C`) gives `IsFinite f.fromNormalization`.
3. `normalization_isFinite_of_locallyAlgebraic` (the form of 0BXS): `f` a `k`-morphism
   (`f.IsOver (Spec k)`) with `Y` locally of finite type over `k` implies `f` locally of finite type
   (`locallyOfFiniteType_of_comp`); apply 2.

## The hypothesis `f.IsOver (Spec k)`

The hypothesis that `f` is a `k`-morphism is implicit in 0BXS ("morphism of locally algebraic
schemes over `k`" means a morphism in the category of `k`-schemes) and cannot be dropped: take
`k = ℚ(t₁, t₂, …)`, `X = Y = Spec k` (with the identity structure morphism, of finite type),
`f = Spec φ` with `φ : k → k`, `tᵢ ↦ tᵢ²`. Then `φ(k) = ℚ(t₁², t₂², …)`, `k/φ(k)` is an infinite
algebraic extension, and the integral closure of `A = k` in `C = k` (via `φ`) is all of `k`, not a
finite `φ(k)`-module, so `fromNormalization` is not finite. The more general form (only requiring
`f` locally of finite type and `X` locally of finite type over `k`) is
`normalization_isFinite_of_locallyOfFiniteType`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Stacks 035S, affine core (via 035B/0335 + 03GH): for `X` locally of finite type
over a field `k`, `Y` reduced and `f : Y ⟶ X` quasi-compact and locally of finite type, the integral closure
of `A = Γ(X, U)` in `Γ(Y, f⁻¹U)` (via `f.app U`) is a finite `A`-module for every affine open `U ⊆ X`.
Proof: `A` is a finitely generated `k`-algebra, hence Noetherian; `f⁻¹U` is a finite union of affine opens
`V ∈ s`; each `Γ(Y, V)` is a reduced finite-type `A`-algebra so the integral closure of `A` in it is finite
(`Algebra.finite_integralClosure_of_finiteType_over_field`); restriction gives an injective `A`-linear map from
the integral closure in `Γ(Y, f⁻¹U)` into the finite product of these (sheaf separatedness), and a submodule of a
finite module over a Noetherian ring is finite. -/
theorem integralClosure_sections_preimage_finite_of_locallyOfFiniteType {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [IsReduced Y]
    (f : Y ⟶ X) [QuasiCompact f] [LocallyOfFiniteType f] (U : X.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    Module.Finite Γ(X, U.1) (integralClosure Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1)) := by
  let _ : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  -- `A = Γ(X, U)` is a finitely generated `k`-algebra, hence Noetherian.
  let g := X ↘ Spec (CommRingCat.of k)
  let φ : k →+* Γ(X, U.1) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appLE ⊤ U.1 le_top).hom
  have hφ : φ.FiniteType := by
    have h1 : (g.appLE ⊤ U.1 le_top).hom.FiniteType :=
      g.finiteType_appLE (isAffineOpen_top _) U.2 _
    have h2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  let _ : Algebra k Γ(X, U.1) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(X, U.1) := hφ
  have : IsNoetherianRing Γ(X, U.1) := Algebra.FiniteType.isNoetherianRing k Γ(X, U.1)
  -- `f⁻¹U` is quasi-compact: a finite union of affine opens `V ∈ s`.
  have hc : IsCompact (f ⁻¹ᵁ U.1 : Set Y) := f.isCompact_preimage U.2.isCompact
  obtain ⟨s, hs, hU⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hc
  have : Finite s := hs.to_subtype
  have hle : ∀ V : s, (V.1 : Y.Opens) ≤ f ⁻¹ᵁ U.1 := fun V => by
    rw [hU]; exact le_iSup₂ (f := fun (i : Y.affineOpens) (_ : i ∈ s) => (i : Y.Opens)) V.1 V.2
  have hcover : f ⁻¹ᵁ U.1 ≤ ⨆ V : s, (V.1 : Y.Opens) := by
    rw [hU]; exact iSup₂_le fun i hi => le_iSup (fun V : s => (V.1 : Y.Opens)) ⟨i, hi⟩
  -- Each `Γ(Y, V)` is a reduced finite-type `A`-algebra via `f.appLE U V`.
  let instB : ∀ V : s, Algebra Γ(X, U.1) Γ(Y, (V.1 : Y.Opens)) :=
    fun V => (f.appLE U.1 V.1 (hle V)).hom.toAlgebra
  have : ∀ V : s, Algebra.FiniteType Γ(X, U.1) Γ(Y, (V.1 : Y.Opens)) :=
    fun V => f.finiteType_appLE U.2 V.1.2 (hle V)
  have : ∀ V : s, Module.Finite Γ(X, U.1) (integralClosure Γ(X, U.1) Γ(Y, (V.1 : Y.Opens))) :=
    fun V => Algebra.finite_integralClosure_of_finiteType_over_field (k := k)
  -- Restriction maps as `A`-algebra homomorphisms.
  let ρ : ∀ V : s, Γ(Y, f ⁻¹ᵁ U.1) →ₐ[Γ(X, U.1)] Γ(Y, (V.1 : Y.Opens)) := fun V =>
    { (Y.presheaf.map (homOfLE (hle V)).op).hom with
      commutes' := fun a => rfl }
  -- The `A`-linear map into the finite product of integral closures.
  let Φ : integralClosure Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) →ₗ[Γ(X, U.1)]
      ∀ V : s, integralClosure Γ(X, U.1) Γ(Y, (V.1 : Y.Opens)) :=
    { toFun := fun x V => ⟨ρ V x.1, IsIntegral.map (ρ V) x.2⟩
      map_add' := fun x y => by
        funext V; ext; simp
      map_smul' := fun a x => by
        funext V; ext; simp }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    ext
    refine Y.sheaf.eq_of_locally_eq' (fun V : s => (V.1 : Y.Opens)) (f ⁻¹ᵁ U.1)
      (fun V => homOfLE (hle V)) hcover x.1 0 fun V => ?_
    have h1 := congrArg Subtype.val (congrFun hx V)
    rw [map_zero]
    exact h1
  exact Module.Finite.of_injective Φ hΦ

/-- Stacks 035S (relative normalization on a Nagata base is finite), in the form used here: `X` locally of
finite type over a field `k` (hence Nagata, 035B), `Y` reduced, `f : Y ⟶ X` quasi-compact, quasi-separated
and locally of finite type; then `f.fromNormalization : f.normalization ⟶ X` is finite. Finiteness is
affine-local on the target (`bridge_isFinite_fromNormalization`), and over an affine open `U ⊆ X` the
normalization is `Spec` of the integral closure of `Γ(X, U)` in `Γ(Y, f⁻¹U)`, which is finite by
`integralClosure_sections_preimage_finite_of_locallyOfFiniteType`. -/
theorem normalization_isFinite_of_locallyOfFiniteType {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [IsReduced Y]
    (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f] :
    IsFinite f.fromNormalization :=
  bridge_isFinite_fromNormalization f fun U =>
    integralClosure_sections_preimage_finite_of_locallyOfFiniteType (k := k) f U

/-- Stacks 0BXS: for a quasi-compact `k`-morphism `f : Y ⟶ X` of locally algebraic `k`-schemes (i.e. `f` commutes
with the structure morphisms, `f.IsOver (Spec k)`) with `Y` reduced, the normalization of `X` in `Y` is finite
over `X`. Since `Y` is locally of finite type over `k` and `f` is a `k`-morphism, `f` is locally of finite type
(`locallyOfFiniteType_of_comp`), and `normalization_isFinite_of_locallyOfFiniteType` applies.
(The hypothesis `f.IsOver (Spec k)` is implicit in Stacks' "morphism of schemes over k"; without it the statement
is false, see the module docstring.) -/
theorem normalization_isFinite_of_locallyAlgebraic {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsReduced Y] (f : Y ⟶ X) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f] :
    AlgebraicGeometry.IsFinite f.fromNormalization := by
  have : LocallyOfFiniteType (f ≫ X ↘ Spec (CommRingCat.of k)) := by
    rw [comp_over]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (X ↘ Spec (CommRingCat.of k))
  exact normalization_isFinite_of_locallyOfFiniteType (k := k) f

end AlgebraicGeometry

end
