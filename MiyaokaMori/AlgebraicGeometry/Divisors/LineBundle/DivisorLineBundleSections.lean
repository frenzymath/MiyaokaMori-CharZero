import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorLocalData
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafAsCokernel
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafLocal
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafStalk
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheaf
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafSheafify
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.SheafOfUnits
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle

/-! # The module sheaf `O_X(D)` of a Cartier divisor

The data of the module sheaf `O_X(D)` of a Cartier divisor `D`: the submodule `lineBundleSections D W`
of `𝒦_X(W)` (`h` belongs to it iff near every point there is a local equation `g` of `D` with
`h·g ∈ O_X`), the restriction maps `lineBundleRestrict`, the presheaf of modules `lineBundlePresheaf`
and the module sheaf `lineBundleModules` (its sheafification), together with auxiliary lemmas: local
equations are preserved by restriction, and two local equations locally differ by a section of `O_X`.
The packaged `CartierDivisor.lineBundle` is in `DivisorLineBundle`; its propositional fields use the
frame theorems built on this module. Source: Hartshorne II.6.13.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `𝒦_X(W)` as a `Γ(X, W)`-module through the structure map `O_X(W) → 𝒦_X(W)`. -/

noncomputable instance CartierDivisor.rationalFunctionsModule {k : Type u} [Field k] (X : Variety k)
    (W : X.toScheme.Opens) :
    Module Γ(X.toScheme, W) (X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op W)) :=
  Module.compHom _ (X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op W)).hom

/-- The condition "`h|_U·g` lies in the image of `O_X(U)`" is preserved by restriction to smaller opens. -/

theorem CartierDivisor.mem_range_restrict {k : Type u} [Field k] {X : Variety k}
    {W U V : X.toScheme.Opens} (hUW : U ≤ W) (hVU : V ≤ U)
    (h : X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op W))
    (g : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (Opposite.op U))
    (hmem : (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hUW).op).hom h *
        ((show (X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U))ˣ from g) :
          X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U)) ∈
        Set.range (X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op U)).hom) :
    (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (hVU.trans hUW)).op).hom h *
        ((show (X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op V))ˣ from
            X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hVU).op g) :
          X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op V)) ∈
        Set.range (X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op V)).hom := by
  obtain ⟨t, ht⟩ := hmem
  refine ⟨(X.toScheme.sheaf.val.map (homOfLE hVU).op).hom t, ?_⟩
  have ht' := congrArg
    ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU).op).hom) ht
  change _ = _ at ht'
  rw [(X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU).op).hom.map_mul] at ht'
  have hnrat := congrArg (fun z => z t) (congrArg CommRingCat.Hom.hom
    (X.toScheme.toRationalFunctionsSheaf.hom.naturality (homOfLE hVU).op))
  change _ = _ at hnrat
  have hnrat' :
      (X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op V)).hom
          ((X.toScheme.sheaf.val.map (homOfLE hVU).op).hom t) =
        (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU).op).hom
          ((X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op U)).hom t) := by
    simpa using hnrat
  have hKeq :
      X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (hVU.trans hUW)).op =
        X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hUW).op ≫
          X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU).op := by
    rw [← Functor.map_comp]
    congr 1
  have hK :
      (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU).op).hom
          ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hUW).op).hom h) =
        (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (hVU.trans hUW)).op).hom h :=
    (congrArg (fun q => q.hom h) hKeq).symm
  rw [hnrat', ht', hK]
  rfl

/-- Restrictions of local equations are local equations: `[g] = D|_U` implies `[g|_V] = D|_V`. -/

theorem CartierDivisor.localEquation_restrict {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) {U V : X.toScheme.Opens} (hVU : V ≤ U)
    (g : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (Opposite.op U))
    (hg : (TopCat.Sheaf.quotient
          (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
          (homOfLE (show U ≤ ⊤ from le_top)).op (Additive.toMul D) =
        (TopCat.Sheaf.quotientπ
          (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).hom.app
          (Opposite.op U) g) :
    (TopCat.Sheaf.quotient
        (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
        (homOfLE (show V ≤ ⊤ from le_top)).op (Additive.toMul D) =
      (TopCat.Sheaf.quotientπ
        (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).hom.app
        (Opposite.op V)
        ((X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hVU).op) g) := by
  have hcompEq :
      (TopCat.Sheaf.quotient
          (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
          (homOfLE (show V ≤ ⊤ from le_top)).op =
        (TopCat.Sheaf.quotient
            (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
            (homOfLE (show U ≤ ⊤ from le_top)).op ≫
          (TopCat.Sheaf.quotient
            (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
            (homOfLE hVU).op := by
    rw [← Functor.map_comp]
    congr 1
  have hcomp :
      (TopCat.Sheaf.quotient
          (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
          (homOfLE (show V ≤ ⊤ from le_top)).op (Additive.toMul D) =
        (TopCat.Sheaf.quotient
            (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
            (homOfLE hVU).op
          ((TopCat.Sheaf.quotient
            (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
            (homOfLE (show U ≤ ⊤ from le_top)).op (Additive.toMul D)) :=
    congrArg (fun q => q.hom (Additive.toMul D)) hcompEq
  rw [hcomp, hg]
  have hn := congrArg (fun z => z g)
    ((TopCat.Sheaf.quotientπ
      (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).hom.naturality
      (homOfLE hVU).op)
  change _ = _ at hn
  exact hn.symm

/-- Two local equations of `D` differ on a smaller neighbourhood by a unit of `O_X`: if
`[g₁] = [g₂] ∈ (𝒦^*/O^*)(U)`, then every `x ∈ U` has a neighbourhood `V ⊆ U` and `c ∈ Γ(X, V)` with
`g₁|_V = c · g₂|_V` (`g₁ g₂⁻¹` lies in the kernel of the quotient map, hence locally comes from `O_X^*`
by `exists_local_preimage_of_quotientπ_eq_one`). -/

theorem CartierDivisor.exists_unit_of_quotientπ_eq {k : Type u} [Field k] {X : Variety k}
    {U : X.toScheme.Opens}
    (g₁ g₂ : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (Opposite.op U))
    (hEq : (TopCat.Sheaf.quotientπ
          (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).hom.app
          (Opposite.op U) g₁ =
        (TopCat.Sheaf.quotientπ
          (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).hom.app
          (Opposite.op U) g₂)
    (x : X.toScheme) (hx : x ∈ U) :
    ∃ (V : X.toScheme.Opens) (_ : x ∈ V) (hVU : V ≤ U) (c : Γ(X.toScheme, V)),
      (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU).op).hom
          ((show (X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U))ˣ from g₁) :
            X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U)) =
        (X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op V)).hom c *
          (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU).op).hom
            ((show (X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U))ˣ from g₂) :
              X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U)) := by
  have hone : (TopCat.Sheaf.quotientπ
      (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).hom.app
      (Opposite.op U) (g₁ * g₂⁻¹) = 1 := by
    rw [map_mul, map_inv, hEq, mul_inv_cancel]
  obtain ⟨V, hxV, hVU, u, hu⟩ :=
    TopCat.Sheaf.exists_local_preimage_of_quotientπ_eq_one
      (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme) U
      (g₁ * g₂⁻¹) hone x hx
  refine ⟨V, hxV, hVU,
    ((show (X.toScheme.sheaf.val.obj (Opposite.op V))ˣ from u) :
      X.toScheme.sheaf.val.obj (Opposite.op V)), ?_⟩
  have key :
      (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme).hom.app
          (Opposite.op V) u *
        (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hVU).op) g₂ =
      (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hVU).op) g₁ := by
    rw [hu, map_mul, map_inv, inv_mul_cancel_right]
  exact congrArg Units.val key.symm

/-- `O_X(D)(W) ⊆ 𝒦_X(W)` (the subsheaf form of Hartshorne II.6.13): `h` belongs to it iff every point
`x ∈ W` has a neighbourhood `U ⊆ W` and a local equation `g ∈ 𝒦^*(U)` of `D` on `U` (i.e.
`[g] = D|_U ∈ (𝒦^*/O^*)(U)`) with `h|_U · g ∈ O_X(U)`. -/

noncomputable def CartierDivisor.lineBundleSections {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) (W : X.toScheme.Opens) :
    Submodule Γ(X.toScheme, W) (X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op W)) where
  carrier := {h | ∀ x ∈ W, ∃ (U : X.toScheme.Opens) (_ : x ∈ U) (hUW : U ≤ W)
      (g : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (Opposite.op U)),
      (TopCat.Sheaf.quotient (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
          (homOfLE le_top : U ⟶ ⊤).op (Additive.toMul D) =
        (TopCat.Sheaf.quotientπ (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).hom.app
          (Opposite.op U) g ∧
      (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hUW).op).hom h *
          ((show (X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U))ˣ from g) :
            X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U)) ∈
        Set.range (X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op U)).hom}
  zero_mem' := by
    intro x hx
    obtain ⟨U, hxU, hUW, g, hg⟩ :=
      TopCat.Sheaf.quotientπ_exists_local
        (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme) W
        ((TopCat.Sheaf.quotient
          (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
          (homOfLE (show W ≤ ⊤ from le_top)).op (Additive.toMul D)) x hx
    refine ⟨U, hxU, hUW, g, ?_, ⟨0, ?_⟩⟩
    · have hcompEq :
          (TopCat.Sheaf.quotient
              (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
              (homOfLE (show U ≤ ⊤ from le_top)).op =
            (TopCat.Sheaf.quotient
                (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
                (homOfLE (show W ≤ ⊤ from le_top)).op ≫
              (TopCat.Sheaf.quotient
                (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
                (homOfLE hUW).op := by
        rw [← Functor.map_comp]
        congr 1
      have hcomp :
          (TopCat.Sheaf.quotient
              (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
              (homOfLE (show U ≤ ⊤ from le_top)).op (Additive.toMul D) =
            (TopCat.Sheaf.quotient
                (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
                (homOfLE hUW).op
              ((TopCat.Sheaf.quotient
                (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
                (homOfLE (show W ≤ ⊤ from le_top)).op (Additive.toMul D)) :=
        congrArg (fun q => q.hom (Additive.toMul D)) hcompEq
      rw [hcomp]
      exact hg
    · rw [map_zero, map_zero, zero_mul]
  add_mem' := by
    rintro h₁ h₂ hh₁ hh₂ x hx
    obtain ⟨U₁, hxU₁, hU₁W, g₁, hg₁, hm₁⟩ := hh₁ x hx
    obtain ⟨U₂, hxU₂, hU₂W, g₂, hg₂, hm₂⟩ := hh₂ x hx
    have h1 : (U₁ ⊓ U₂ : X.toScheme.Opens) ≤ U₁ := inf_le_left
    have h2 : (U₁ ⊓ U₂ : X.toScheme.Opens) ≤ U₂ := inf_le_right
    have hxU : x ∈ (U₁ ⊓ U₂ : X.toScheme.Opens) := ⟨hxU₁, hxU₂⟩
    obtain ⟨V, hxV, hVU, c, hc⟩ := CartierDivisor.exists_unit_of_quotientπ_eq
      (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE h1).op g₁)
      (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE h2).op g₂)
      ((CartierDivisor.localEquation_restrict D h1 g₁ hg₁).symm.trans
        (CartierDivisor.localEquation_restrict D h2 g₂ hg₂)) x hxU
    have hVU₁ : V ≤ U₁ := hVU.trans h1
    have hVU₂ : V ≤ U₂ := hVU.trans h2
    refine ⟨V, hxV, hVU₁.trans hU₁W,
      X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hVU₁).op g₁,
      CartierDivisor.localEquation_restrict D hVU₁ g₁ hg₁, ?_⟩
    obtain ⟨s₁, hs₁⟩ := CartierDivisor.mem_range_restrict hU₁W hVU₁ h₁ g₁ hm₁
    obtain ⟨s₂, hs₂⟩ := CartierDivisor.mem_range_restrict hU₂W hVU₂ h₂ g₂ hm₂
    have hresEq : ∀ {U' : X.toScheme.Opens} (hU' : (U₁ ⊓ U₂ : X.toScheme.Opens) ≤ U')
        (hVU' : V ≤ U') (g : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (Opposite.op U')),
        (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU).op).hom
            ((show (X.toScheme.rationalFunctionsSheaf.val.obj
                (Opposite.op (U₁ ⊓ U₂ : X.toScheme.Opens)))ˣ from
              X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hU').op g) :
              X.toScheme.rationalFunctionsSheaf.val.obj
                (Opposite.op (U₁ ⊓ U₂ : X.toScheme.Opens))) =
          ((show (X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op V))ˣ from
              X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hVU').op g) :
            X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op V)) := by
      intro U' hU' hVU' g
      have heq :
          X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU').op =
            X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hU').op ≫
              X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU).op := by
        rw [← Functor.map_comp]
        congr 1
      exact (congrArg (fun q => q.hom
        ((show (X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U'))ˣ from g) :
          X.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U'))) heq).symm
    rw [hresEq h1 hVU₁ g₁, hresEq h2 hVU₂ g₂] at hc
    refine ⟨s₁ + (show X.toScheme.sheaf.val.obj (Opposite.op V) from c) * s₂, ?_⟩
    rw [map_add, map_mul, hs₁, hs₂, map_add, hc]
    ring
  smul_mem' c h hh := by
    intro x hx
    obtain ⟨U, hxU, hUW, g, hg, t, ht⟩ := hh x hx
    refine ⟨U, hxU, hUW, g, hg,
      ⟨(X.toScheme.sheaf.val.map (homOfLE hUW).op).hom c * t, ?_⟩⟩
    rw [map_mul, ht]
    have hnat := congrArg (fun f => f c) (congrArg CommRingCat.Hom.hom
      (X.toScheme.toRationalFunctionsSheaf.hom.naturality (homOfLE hUW).op))
    change _ = _ at hnat
    have hres : (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hUW).op).hom
        ((X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op W)).hom c * h) =
      (X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op U)).hom
        ((X.toScheme.sheaf.val.map (homOfLE hUW).op).hom c) *
      (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hUW).op).hom h := by
      rw [(X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hUW).op).hom.map_mul]
      congr 1
      exact hnat.symm
    change _ = (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hUW).op).hom
        ((X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op W)).hom c * h) * _
    rw [hres, mul_assoc]

set_option backward.isDefEq.respectTransparency false in

/-- The restriction maps: the restriction of `𝒦_X` restricted to the submodules (semilinear with respect to
`Γ(X, W) → Γ(X, W')`). -/

noncomputable def CartierDivisor.lineBundleRestrict {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) {W W' : X.toScheme.Opens} (i : W' ⟶ W) :
    CartierDivisor.lineBundleSections D W →ₛₗ[(X.toScheme.presheaf.map i.op).hom]
      CartierDivisor.lineBundleSections D W' where
  toFun h := ⟨(X.toScheme.rationalFunctionsSheaf.val.map i.op).hom h.1, by
    intro x hx
    rcases h.2 x (i.le hx) with ⟨U, hxU, hUW, g, hg, hprod⟩
    let f : U ⊓ W' ⟶ U := homOfLE inf_le_left
    let g' := (X.toScheme.rationalFunctionsUnitsSheaf.val.map f.op).hom g
    refine ⟨U ⊓ W', ⟨hxU, hx⟩, inf_le_right, g', ?_, ?_⟩
    · have hn := congrArg (fun z => z g)
        ((TopCat.Sheaf.quotientπ
          (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).hom.naturality f.op)
      change _ = _ at hn
      have hcomp :
          ((TopCat.Sheaf.quotient
            (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
            (homOfLE (show U ⊓ W' ≤ ⊤ from (inf_le_left.trans hUW).trans le_top)).op).hom
            (Additive.toMul D) =
          ((TopCat.Sheaf.quotient
            (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map f.op).hom
            (((TopCat.Sheaf.quotient
              (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
              (homOfLE (show U ≤ ⊤ from hUW.trans le_top)).op).hom (Additive.toMul D)) := by
        have heq :
            (TopCat.Sheaf.quotient
              (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
                (homOfLE (show U ⊓ W' ≤ ⊤ from (inf_le_left.trans hUW).trans le_top)).op =
              (TopCat.Sheaf.quotient
                (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
                  (homOfLE (show U ≤ ⊤ from hUW.trans le_top)).op ≫
                (TopCat.Sheaf.quotient
                  (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map f.op := by
          rw [← Functor.map_comp]
          congr 1
        exact congrArg (fun q => q.hom (Additive.toMul D)) heq
      rw [hcomp, hg]
      exact hn.symm
    · rcases hprod with ⟨t, ht⟩
      refine ⟨(X.toScheme.sheaf.val.map f.op).hom t, ?_⟩
      have ht' := congrArg ((X.toScheme.rationalFunctionsSheaf.val.map f.op).hom) ht
      change _ = _ at ht'
      rw [(X.toScheme.rationalFunctionsSheaf.val.map f.op).hom.map_mul] at ht'
      have hnrat := congrArg (fun z => z t) (congrArg CommRingCat.Hom.hom
        (X.toScheme.toRationalFunctionsSheaf.hom.naturality f.op))
      change _ = _ at hnrat
      have hK :
          (X.toScheme.rationalFunctionsSheaf.val.map f.op).hom
              ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hUW).op).hom ↑h) =
            (X.toScheme.rationalFunctionsSheaf.val.map
              (homOfLE (show U ⊓ W' ≤ W from inf_le_left.trans hUW)).op).hom ↑h := by
        have heq := X.toScheme.rationalFunctionsSheaf.val.map_comp
          (homOfLE hUW).op f.op
        have heq' := congrArg (fun q => q.hom ↑h) heq
        exact heq'.symm
      have hKi :
          (X.toScheme.rationalFunctionsSheaf.val.map
              (homOfLE (show U ⊓ W' ≤ W from inf_le_left.trans hUW)).op).hom ↑h =
            (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (show U ⊓ W' ≤ W' from
              inf_le_right)).op).hom
              ((X.toScheme.rationalFunctionsSheaf.val.map i.op).hom ↑h) := by
        have heq := X.toScheme.rationalFunctionsSheaf.val.map_comp i.op
          (homOfLE (show U ⊓ W' ≤ W' from inf_le_right)).op
        have heq' := congrArg (fun q => q.hom ↑h) heq
        exact heq'
      have hnrat' :
          (X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op (U ⊓ W'))).hom
              ((X.toScheme.sheaf.val.map f.op).hom t) =
            (X.toScheme.rationalFunctionsSheaf.val.map f.op).hom
              ((X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op U)).hom t) := by
        simpa using hnrat
      rw [hnrat', ht', hK, hKi]
      rfl⟩
  map_add' h h' := Subtype.ext (map_add _ _ _)
  map_smul' r h := by
    apply Subtype.ext
    change (X.toScheme.rationalFunctionsSheaf.val.map i.op).hom
        ((X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op W)).hom r * h.1) =
      (X.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op W')).hom
        ((X.toScheme.presheaf.map i.op).hom r) *
        (X.toScheme.rationalFunctionsSheaf.val.map i.op).hom h.1
    rw [(X.toScheme.rationalFunctionsSheaf.val.map i.op).hom.map_mul]
    congr 1
    have hn := congrArg (fun f => f r) (congrArg CommRingCat.Hom.hom
      (X.toScheme.toRationalFunctionsSheaf.hom.naturality i.op))
    change _ = _ at hn
    exact hn.symm

set_option backward.isDefEq.respectTransparency false in

/-- `O_X(D)` as a presheaf of `O_X`-modules. -/

noncomputable def CartierDivisor.lineBundlePresheaf {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) : X.toScheme.PresheafOfModules where
  obj W := ModuleCat.of Γ(X.toScheme, W.unop) (CartierDivisor.lineBundleSections D W.unop)
  map {W W'} i := ModuleCat.ofHom (Y :=
      (ModuleCat.restrictScalars (X.toScheme.ringCatSheaf.obj.map i).hom).obj
        (ModuleCat.of Γ(X.toScheme, W'.unop) (CartierDivisor.lineBundleSections D W'.unop)))
    { toFun := CartierDivisor.lineBundleRestrict D i.unop
      map_add' := (CartierDivisor.lineBundleRestrict D i.unop).map_add
      map_smul' := (CartierDivisor.lineBundleRestrict D i.unop).map_smulₛₗ }
  map_id W := by
    ext h
    apply Subtype.ext
    exact congrArg (fun q => q.hom h.1) (X.toScheme.rationalFunctionsSheaf.val.map_id W)
  map_comp i j := by
    ext h
    apply Subtype.ext
    exact congrArg (fun q => q.hom h.1) (X.toScheme.rationalFunctionsSheaf.val.map_comp i j)

/-- `O_X(D)` as a sheaf of `O_X`-modules (the sheafification; the presheaf is already a sheaf, so
sheafification does not change it). -/

noncomputable def CartierDivisor.lineBundleModules {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) : X.toScheme.Modules :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.toScheme.ringCatSheaf.obj)).obj
    (CartierDivisor.lineBundlePresheaf D)

end
