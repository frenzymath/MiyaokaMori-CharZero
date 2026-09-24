import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyShift
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHPrimeSections
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.SchemeModulesEnoughInjectives
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks09sy

/-! # Leray degeneration for a morphism of schemes

**Leray degeneration for a morphism of schemes, affine-basis form** (Stacks 01F4(1),
cohomology-lemma-apply-Leray; Hartshorne III Ex. 8.1): let `f : X → Y` be a morphism of schemes and
`M` an `O_X`-module such that `H^q(f⁻¹V, M) = 0` for every affine open `V ⊆ Y` and every `q > 0`
(this says exactly that the higher direct images `R^q f_* M` vanish, since `R^q f_* M` is the
sheafification of `V ↦ H^q(f⁻¹V, M)` and the affine opens form a basis). Then
`H^p(X, M) ≃+ H^p(Y, f_* M)` for every `p`.

The main use is Stacks 089W (`Stacks089w.lean`): for an affine morphism `f` and a quasi-coherent `M`,
the hypothesis is Serre vanishing on the affine opens `f⁻¹V` (Stacks 01XB).

## Proof (dimension shifting; no spectral sequence, no derived categories)
This is the argument of Hartshorne III.4.5 (p. 222) with the Čech complex replaced by `f_*`,
exactly as in `CechLeray.lean`.
Induction on `p`, for all `M` at once.
1. `p = 0`: `H^0(X, M) = Γ(X, M) = Γ(Y, f_* M) = H^0(Y, f_* M)` (Mathlib `Sheaf.H.equiv₀`;
   `Γ(Y, f_*M) = Γ(X, M)` holds by definition since `f⁻¹(⊤) = ⊤` is `rfl`).
2. `p ≥ 1`: choose `0 → M → I → R → 0` with `I` an injective `O_X`-module
   (`X.Modules` has enough injectives).
   * `f_*` is a right adjoint (Mathlib `pullbackPushforwardAdjunction`), hence left exact, so
     `0 → f_*M → f_*I → f_*R` is exact and `f_*M → f_*I` is mono.
   * `f_*I → f_*R` is an epimorphism: a map of `O_Y`-modules is epi iff locally surjective on
     sections (`epi_iff_locally_surjective_sections`); on an affine `V`, `Γ(f⁻¹V, I) → Γ(f⁻¹V, R)`
     is surjective because `H^1(f⁻¹V, M) = 0` (`surjective_sections_of_hPrime_one`), and the affine
     opens form a basis (Mathlib `Scheme.isBasis_affineOpens`). Hence `0 → f_*M → f_*I → f_*R → 0`
     is short exact in `Y.Modules`.
   * `I` is flasque (Stacks 09SX, `isFlasque_of_injective`), `f_*I` is flasque (restriction maps
     of `f_*I` are restriction maps of `I`), so `H^k(X, I) = 0` and `H^k(Y, f_*I) = 0` for `k > 0`
     (Stacks 09SY, `TopCat.Sheaf.H_subsingleton_of_isFlasque`; that theorem lives at `Ext`
     universe `u`, and `Ext.chgUniv` transports it to the universe `u+1` used by
     `sheafCohomology`).
   * `R` again satisfies the hypothesis: `H^q(f⁻¹V, R) = 0` from `H^q(f⁻¹V, I) = 0` and
     `H^{q+1}(f⁻¹V, M) = 0` (`hPrime_subsingleton_quotient`).
   * `p = 1`: both `H^1(X, M)` and `H^1(Y, f_*M)` are `coker(Γ(I) → Γ(R))`
     (`sheafCohomology.one_equiv_quotient` on `X` and on `Y`), and the two cokernels are the same
     abelian group (`quotient_addEquiv_pushforward`: the two quotient descriptions differ only in
     the ring of scalars).
   * `p = j + 2`: the connecting maps `H^{j+1}(X, R) → H^{j+2}(X, M)` and
     `H^{j+1}(Y, f_*R) → H^{j+2}(Y, f_*M)` are bijective (`sheafCohomology.δ_bijective`), and the
     induction hypothesis applied to `R` gives `H^{j+1}(X, R) ≃+ H^{j+1}(Y, f_*R)`.

Only additive isomorphisms are produced (the target statement of 089W asks for `≃+`); the maps are
in fact `Γ(Y, O_Y)`-linear but this is not recorded.

Source: Stacks 01F4(1) (apply-Leray), 01F2 (Leray), 089W; Hartshorne III Ex. 8.1, III.4.5.
Fully proved: `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- `f_*` of a flasque module sheaf is flasque: the restriction maps of `f_* M` are restriction
maps of `M` (along `f⁻¹V ⊆ f⁻¹U`). -/
theorem isFlasque_pushforward (M : X.Modules) [hM : TopCat.Sheaf.IsFlasque M.toAddCommGrpSheaf] :
    TopCat.Sheaf.IsFlasque ((pushforward f).obj M).toAddCommGrpSheaf where
  epi {_U _V} i := hM.epi ((Opens.map f.base).map i.unop).op

/-- Higher cohomology of `f_* I` vanishes for `I` injective (`f_* I` is flasque, Stacks 09SY),
stated for the `u+1`-universe `Sheaf.H` used by `sheafCohomology` (Stacks 09SY is stated at `Ext`
universe `u`; `Ext.chgUniv` transports it). -/
theorem subsingleton_sheafCohomology_pushforward_of_injective (I : X.Modules) [Injective I]
    (k : ℕ) :
    Subsingleton (AlgebraicGeometry.sheafCohomology Y ((pushforward f).obj I) (k + 1)) := by
  have hfl : TopCat.Sheaf.IsFlasque I.toAddCommGrpSheaf := isFlasque_of_injective I
  have hfl' : TopCat.Sheaf.IsFlasque ((pushforward f).obj I).toAddCommGrpSheaf :=
    isFlasque_pushforward f I
  have h := TopCat.Sheaf.H_subsingleton_of_isFlasque
    ((pushforward f).obj I).toAddCommGrpSheaf (k + 1) (Nat.succ_pos k)
  exact (Abelian.Ext.chgUniv.{u}).subsingleton

/-- `H^0`: `Γ(Y, f_*M) = Γ(X, M)` (by definition, since `f⁻¹(⊤) = ⊤` is `rfl`). -/
theorem sheafCohomology_pushforward_addEquiv_zero (M : X.Modules) :
    Nonempty (CategoryTheory.Sheaf.H M.toAddCommGrpSheaf 0 ≃+
      CategoryTheory.Sheaf.H ((pushforward f).obj M).toAddCommGrpSheaf 0) :=
  ⟨(Sheaf.H.equiv₀ M.toAddCommGrpSheaf (Limits.isTerminalTop (α := X.Opens))).trans
    (Sheaf.H.equiv₀ ((pushforward f).obj M).toAddCommGrpSheaf
      (Limits.isTerminalTop (α := Y.Opens))).symm⟩

/-- `f_* g` is an epimorphism when `H^1(f⁻¹V, M) = 0` on all affine opens `V ⊆ Y`
(local surjectivity on sections over the affine basis). -/
theorem epi_pushforward_map_of_hPrime_one (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h1 : ∀ V : Y.affineOpens, Subsingleton (S.X₁.toAddCommGrpSheaf.H' 1 (f ⁻¹ᵁ V.1))) :
    Epi ((pushforward f).map S.g) := by
  rw [epi_iff_locally_surjective_sections]
  intro U s p hp
  obtain ⟨V, hV, hpV, hVU⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hp
  refine ⟨V, hVU, hpV, ?_⟩
  obtain ⟨y, hy⟩ := surjective_sections_of_hPrime_one S hS (f ⁻¹ᵁ V) (h1 ⟨V, hV⟩)
    (S.X₃.presheaf.map ((Opens.map f.base).map (homOfLE hVU)).op s)
  exact ⟨y, hy⟩

/-- `f_*` of a short exact sequence is short exact as soon as `f_* g` is epi (`f_*` is a right
adjoint, hence left exact). -/
theorem shortExact_map_pushforward (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hepi : Epi ((pushforward f).map S.g)) :
    (S.map (pushforward f)).ShortExact := by
  have hmono := hS.mono_f
  have hlim : PreservesLimitsOfSize.{0, 0} (pushforward f) :=
    (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
  have hpm : (pushforward f).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  exact
    { exact := hS.exact.map_of_mono_of_preservesKernel (pushforward f) hmono inferInstance
      mono_f := (pushforward f).map_mono S.f
      epi_g := hepi }

/-- The two descriptions of `coker(Γ(I) → Γ(R))` — as a quotient of `Γ(X, O_X)`-modules on `X`
and as a quotient of `Γ(Y, O_Y)`-modules on `Y` — are the same abelian group. -/
theorem quotient_addEquiv_pushforward (S : ShortComplex X.Modules) :
    Nonempty ((Γ(S.X₃, ⊤) ⧸ LinearMap.range (Scheme.Modules.Hom.appTopLinear S.g)) ≃+
      (Γ((S.map (pushforward f)).X₃, ⊤) ⧸
        LinearMap.range (Scheme.Modules.Hom.appTopLinear (S.map (pushforward f)).g))) := by
  let pX := LinearMap.range (Scheme.Modules.Hom.appTopLinear S.g)
  let pY := LinearMap.range (Scheme.Modules.Hom.appTopLinear (S.map (pushforward f)).g)
  let qX : Γ(S.X₃, ⊤) →+ Γ(S.X₃, ⊤) ⧸ pX := pX.mkQ.toAddMonoidHom
  let qY : Γ(S.X₃, ⊤) →+ Γ((S.map (pushforward f)).X₃, ⊤) ⧸ pY := pY.mkQ.toAddMonoidHom
  have hker : qX.ker = qY.ker := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero pX).1 hx)
      exact (Submodule.Quotient.mk_eq_zero pY).2 (LinearMap.mem_range.2 ⟨y, hy⟩)
    · intro hx
      obtain ⟨y, hy⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero pY).1 hx)
      exact (Submodule.Quotient.mk_eq_zero pX).2 (LinearMap.mem_range.2 ⟨y, hy⟩)
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective qX (Submodule.mkQ_surjective pX)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective qY (Submodule.mkQ_surjective pY)))⟩

/-- The `p = 1` step: `H^1(X, M) ≃+ H^1(Y, f_*M)` when `0 → M → I → R → 0` and its pushforward are
short exact and `H^1` of the middle terms vanishes. -/
theorem sheafCohomology_pushforward_addEquiv_one (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hT : (S.map (pushforward f)).ShortExact)
    [Subsingleton (AlgebraicGeometry.sheafCohomology X S.X₂ 1)]
    [Subsingleton (AlgebraicGeometry.sheafCohomology Y (S.map (pushforward f)).X₂ 1)] :
    Nonempty (CategoryTheory.Sheaf.H S.X₁.toAddCommGrpSheaf 1 ≃+
      CategoryTheory.Sheaf.H ((pushforward f).obj S.X₁).toAddCommGrpSheaf 1) := by
  obtain ⟨dX⟩ := AlgebraicGeometry.sheafCohomology.one_equiv_quotient hS
  obtain ⟨dY⟩ := AlgebraicGeometry.sheafCohomology.one_equiv_quotient hT
  obtain ⟨q⟩ := quotient_addEquiv_pushforward f S
  exact ⟨dX.toAddEquiv.trans (q.trans dY.toAddEquiv.symm)⟩

/-- The shift step: `H^{j+2}(X, M) ≃+ H^{j+2}(Y, f_*M)` from `H^{j+1}(X, R) ≃+ H^{j+1}(Y, f_*R)`,
when the middle terms are acyclic in degrees `j+1`, `j+2`. -/
theorem sheafCohomology_pushforward_addEquiv_succ (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hT : (S.map (pushforward f)).ShortExact) (j : ℕ)
    [Subsingleton (AlgebraicGeometry.sheafCohomology X S.X₂ (j + 1))]
    [Subsingleton (AlgebraicGeometry.sheafCohomology X S.X₂ (j + 1 + 1))]
    [Subsingleton (AlgebraicGeometry.sheafCohomology Y (S.map (pushforward f)).X₂ (j + 1))]
    [Subsingleton (AlgebraicGeometry.sheafCohomology Y (S.map (pushforward f)).X₂ (j + 1 + 1))]
    (r : CategoryTheory.Sheaf.H S.X₃.toAddCommGrpSheaf (j + 1) ≃+
      CategoryTheory.Sheaf.H ((pushforward f).obj S.X₃).toAddCommGrpSheaf (j + 1)) :
    Nonempty (CategoryTheory.Sheaf.H S.X₁.toAddCommGrpSheaf (j + 1 + 1) ≃+
      CategoryTheory.Sheaf.H ((pushforward f).obj S.X₁).toAddCommGrpSheaf (j + 1 + 1)) := by
  -- `LinearEquiv.ofBijective _ …` (not `AddEquiv.ofBijective (δ …).toAddMonoidHom`): the latter
  -- makes the kernel unfold `δ` through the coercion mismatch and costs 20 s of type checking.
  let dX := LinearEquiv.ofBijective _
    (AlgebraicGeometry.sheafCohomology.δ_bijective hS (j + 1) (j + 1 + 1) rfl)
  let dY := LinearEquiv.ofBijective _
    (AlgebraicGeometry.sheafCohomology.δ_bijective hT (j + 1) (j + 1 + 1) rfl)
  exact ⟨dX.toAddEquiv.symm.trans (r.trans dY.toAddEquiv)⟩

/-- **Leray degeneration** (Stacks 01F4(1), affine-basis form): if `H^q(f⁻¹V, M) = 0` for all
affine opens `V ⊆ Y` and all `q > 0`, then `H^p(X, M) ≃+ H^p(Y, f_*M)` for all `p`. -/
theorem sheafCohomology_pushforward_addEquiv_of_hPrime_vanishing (p : ℕ) :
    ∀ (M : X.Modules),
      (∀ (V : Y.affineOpens) (q : ℕ), 0 < q →
        Subsingleton (M.toAddCommGrpSheaf.H' q (f ⁻¹ᵁ V.1))) →
      Nonempty (CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p ≃+
        CategoryTheory.Sheaf.H ((pushforward f).obj M).toAddCommGrpSheaf p) := by
  induction p with
  | zero =>
    intro M _
    exact sheafCohomology_pushforward_addEquiv_zero f M
  | succ i ih =>
    intro M hM
    -- 0 → M → I → R → 0 with I injective
    let S : ShortComplex X.Modules :=
      ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel (Injective.ι M)
        mono_f := inferInstanceAs (Mono (Injective.ι M))
        epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι M))) }
    have hinj : Injective S.X₂ := inferInstanceAs (Injective (Injective.under M))
    have hepi : Epi ((pushforward f).map S.g) :=
      epi_pushforward_map_of_hPrime_one f S hS (fun V => hM V 1 one_pos)
    have hT : (S.map (pushforward f)).ShortExact := shortExact_map_pushforward f S hS hepi
    have hR : ∀ (V : Y.affineOpens) (q : ℕ), 0 < q →
        Subsingleton (S.X₃.toAddCommGrpSheaf.H' q (f ⁻¹ᵁ V.1)) := fun V q hq =>
      hPrime_subsingleton_quotient S hS _ q (hPrime_subsingleton_of_injective S.X₂ _ q hq)
        (hM V (q + 1) (Nat.succ_pos q))
    have hXI : ∀ k : ℕ, Subsingleton (AlgebraicGeometry.sheafCohomology X S.X₂ (k + 1)) := fun k =>
      AlgebraicGeometry.sheafCohomology.subsingleton_of_injective S.X₂ k
    have hYI : ∀ k : ℕ,
        Subsingleton (AlgebraicGeometry.sheafCohomology Y (S.map (pushforward f)).X₂ (k + 1)) :=
      fun k => subsingleton_sheafCohomology_pushforward_of_injective f S.X₂ k
    cases i with
    | zero =>
      have := hXI 0
      have := hYI 0
      exact sheafCohomology_pushforward_addEquiv_one f S hS hT
    | succ j =>
      have := hXI j
      have := hXI (j + 1)
      have := hYI j
      have := hYI (j + 1)
      obtain ⟨r⟩ := ih S.X₃ hR
      exact sheafCohomology_pushforward_addEquiv_succ f S hS hT j r

end AlgebraicGeometry.Scheme.Modules

end
