import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus

/-! # A section generates the stalk away from its zero scheme

For a global section `σ` of a line bundle `M`, the germ of `σ` generates the stalk `M_y` at every point `y`
outside the support of the zero scheme `Z(σ)`. Consequences: (C0) if `X` is integral and `Z(σ) ≠ X`, the
germ of `σ` at the generic point is nonzero; (C1) if `X` is integral and locally Noetherian, `ord_y(σ) = 0`
outside `Z(σ)`.
Sources: Stacks 01WX, 01X0 (effective Cartier divisors and sections of invertible sheaves: on a trivializing
open `U` the ideal sheaf of `Z(σ)` is `(f)` where `σ|_U = f·e`); Stacks 02SE (local computation of `div_L(s)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.Scheme.Modules

/-- If `y` is not in the support of `Z(σ)`, the germ of `σ` at `y` generates `M_y`.

Sources: Stacks 01WX, 01X0 (the ideal sheaf of `Z(σ)` is generated on a trivialization by the local equation
of `σ`); Mathlib `IdealSheafData.mem_support_iff_of_mem`.

Proof:
1. Take a trivialization at `y` (`Scheme.Modules.exists_trivialization M y`): an open `U ∋ y` and
   `eU : M|_U ≅ O_U`. Take an affine open `V ∋ y` inside `U`; `eU` restricted to `V` gives `Γ(M,V) ≅ Γ(X,V)`
   (`Γ(X,V)`-linear); put `e := eU⁻¹(1) ∈ Γ(M,V)`, so `σ|_V = f·e` with `f ∈ Γ(X,V)`.
2. The ideal `I(V) := span{φ(σ|_V) | φ : Γ(M,V) →ₗ Γ(X,V)}` (the definition of `idealSheafOfSection`) equals
   `(f)`: `⊆` since `φ(σ|_V) = f·φ(e)`; `⊇` by taking `φ :=` the section isomorphism of `eU` on `V`, for which
   `φ(σ|_V) = f`.
3. `y ∉ support` gives, by `IdealSheafData.mem_support_iff_of_mem` (`V ∋ y`), `y ∉ X.zeroLocus (I(V))`, i.e.
   there is `a ∈ I(V) = (f)` with `y ∈ X.basicOpen a`; `a = c·f`, so `y ∈ X.basicOpen f`
   (`Scheme.basicOpen_mul`), i.e. the germ of `f` at `y` is a unit of `O_{X,y}` (`Scheme.mem_basicOpen`).
4. On stalks, `germ_y σ = (germ_y f)·(germ_y e)`, and `germ_y e` generates `M_y` (it corresponds to `1` under
   the stalk isomorphism `lineStalkEquivOfTrivialization X M U ⟨y, _⟩ eU`); a unit multiple of a generator
   is a generator, so `span{germ_y σ} = ⊤`.
Edge cases: if `σ = 0` then `I(V) = 0` and `support = X`, so the hypothesis fails; for `M` trivial and
`X = Spec A` this is "`f ∉ p_y` implies `f` invertible in `A_{p_y}`". -/
theorem idealSheafOfSection_germ_span_eq_top_of_notMem_support {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsLineBundle] (σ : (M.val.obj (Opposite.op ⊤) : Type u)) {y : X}
    (hy : y ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection M σ).support) :
    Submodule.span (X.presheaf.stalk y)
      {M.presheaf.germ ⊤ y trivial (show Γ(M, ⊤) from σ)} = ⊤ := by
  obtain ⟨W, hW, -, hyW, e, hf⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le M (U := ⊤) (p := y) trivial
  set σW : Γ(M, W) := M.res (le_top : W ≤ ⊤) (show Γ(M, ⊤) from σ) with hσW
  set c := hf.coord le_rfl σW with hcdef
  have hc : c • M.res le_rfl e = σW := hf.coord_smul_frame le_rfl σW
  -- I(W) ⊆ (c): φ(σ|_W) = φ(c • e) = c · φ(e)
  have hI : (AlgebraicGeometry.Scheme.idealSheafOfSection M σ).ideal ⟨W, hW⟩ ≤ Ideal.span {c} := by
    show Ideal.span (Set.range fun φ : Γ(M, W) →ₗ[Γ(X, W)] Γ(X, W) =>
      φ (M.presheaf.map (CategoryTheory.homOfLE le_top).op (show Γ(M, ⊤) from σ))) ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    show φ σW ∈ Ideal.span {c}
    rw [← hc, _root_.map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
  -- y ∉ Z(σ), so some element of I(W) is invertible at y, hence c is invertible at y
  have hyI := mt (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := AlgebraicGeometry.Scheme.idealSheafOfSection M σ) (U := ⟨W, hW⟩) hyW).mpr hy
  rw [AlgebraicGeometry.Scheme.mem_zeroLocus_iff] at hyI
  push Not at hyI
  obtain ⟨a, haI, hya⟩ := hyI
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp (hI haI)
  rw [AlgebraicGeometry.Scheme.basicOpen_mul] at hya
  have hu : IsUnit (X.presheaf.germ W y hyW c) := (X.mem_basicOpen c y hyW).mp hya.2
  -- germ_y σ = (germ_y c) • (germ_y e), and germ_y e generates the stalk
  have h1 : M.presheaf.germ ⊤ y trivial (show Γ(M, ⊤) from σ) = M.presheaf.germ W y hyW σW :=
    (TopCat.Presheaf.germ_res_apply M.presheaf (CategoryTheory.homOfLE (le_top : W ≤ ⊤)) y hyW _).symm
  have hgerm : M.presheaf.germ ⊤ y trivial (show Γ(M, ⊤) from σ) =
      X.presheaf.germ W y hyW c • M.presheaf.germ W y hyW e := by
    rw [h1, ← hc, AlgebraicGeometry.Scheme.Modules.germ_smul',
      AlgebraicGeometry.Scheme.Modules.res_self]
  rw [hgerm, Submodule.span_singleton_smul_eq hu]
  exact hf.span_germ_eq_top hyW

/-- The specialization map sends the germ at `y` to the germ at the generic point
(`moduleStalkToGenericFiber_germ` for `U = ⊤`). -/
theorem moduleStalkToGenericFiber_germ_top {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (M : X.Modules) (σ : (M.val.obj (Opposite.op ⊤) : Type u))
    (y : X) :
    moduleStalkToGenericFiber X M y (M.presheaf.germ ⊤ y trivial (show Γ(M, ⊤) from σ)) =
      M.presheaf.germ ⊤ (genericPoint X) trivial (show Γ(M, ⊤) from σ) :=
  moduleStalkToGenericFiber_germ X M y ⊤ trivial _

/-- (C0) For `X` integral: if some point lies outside `Z(σ)`, the germ of `σ` at the generic point is nonzero. -/
theorem germ_genericPoint_ne_zero_of_notMem_support {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (M : X.Modules) [M.IsLineBundle]
    (σ : (M.val.obj (Opposite.op ⊤) : Type u)) {y : X}
    (hy : y ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection M σ).support) :
    M.presheaf.germ ⊤ (genericPoint X) trivial (show Γ(M, ⊤) from σ) ≠ 0 := by
  intro h0
  have ht := idealSheafOfSection_germ_span_eq_top_of_notMem_support M σ hy
  obtain ⟨s, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero M
  obtain ⟨g, hg⟩ := AlgebraicGeometry.Scheme.Modules.exists_smul_toGenericFiber_eq M y _ ht s
  rw [moduleStalkToGenericFiber_germ_top, h0, smul_zero] at hg
  exact hs hg.symm

/-- (C1) For `X` integral and locally Noetherian: `ord_y(σ_η) = 0` outside `Z(σ)`. -/
theorem rationalSectionOrd_germ_eq_zero_of_notMem_support {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    (M : X.Modules) [M.IsLineBundle] (σ : (M.val.obj (Opposite.op ⊤) : Type u)) {y : X}
    (hy : y ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection M σ).support) :
    M.rationalSectionOrd (M.presheaf.germ ⊤ (genericPoint X) trivial (show Γ(M, ⊤) from σ)) y
      = 0 := by
  have ht := idealSheafOfSection_germ_span_eq_top_of_notMem_support M σ hy
  rw [AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_eq_ord_of_generator M y _ ht 1 _
    (germ_genericPoint_ne_zero_of_notMem_support M σ hy)
    (by rw [one_smul, moduleStalkToGenericFiber_germ_top])]
  have h1 := AlgebraicGeometry.Scheme.Modules.ord_algebraMap_of_isUnit y
    (isUnit_one (M := X.presheaf.stalk y))
  rwa [map_one] at h1

end AlgebraicGeometry.Scheme

end
