import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjMapTwistComparison
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01n2TwistStalkNormalize

/-! # Stacks 01N2 for the twisting sheaves: bijectivity on stalks

**Stacks 01N2, last sentence (via 01MX), on stalks.** Setting as in `Stacks01n2`: `B = R' ⊗_R A` as graded algebras
(`f : 𝒜 →+*ᵍ ℬ`, `fR`, `hfR`, `hbc : IsBaseChange R' fR`), `ρ := Proj.map f hf : Proj ℬ ⟶ Proj 𝒜`,
`θ := Proj.twistPullbackHom f hf n : ρ^* O_{Proj 𝒜}(n) ⟶ O_{Proj ℬ}(n)` (`ProjMapTwistComparison`).

Statement (`twistPullbackHom_stalkMap_comp_tensorMap_bijective`): for every `y ∈ Proj ℬ` the composite
`Θ_y : O_{B,y} ⊗_{O_{A,x}} O_A(n)_x → (ρ^* O_A(n))_y → O_B(n)_y` (`x := ρ y`) of the pullback-stalk tensor
map `T` (`modulePullbackStalkTensorMap`, bijective by `modulePullbackStalkTensorMap_bijective`)
with the stalk map of `θ` is bijective. Together with `moduleHom_isIso_iff_stalk_bijective` this
gives `IsIso θ` (`Proj.isIso_twistPullbackHom` in `Stacks01n2`).

The proof is split over three modules:
* `Stacks01n2TwistStalkAlgebra`: the chart-level algebra
  `(B_{f s})_n = R' ⊗_R (A_s)_n` (`twistAwayLift_bijective`), the degree-`n` analogue of
  `Stacks01n2AwayBaseChange.awayLift_bijective`;
* `Stacks01n2TwistStalkSections`: sections and germs of `O(n)`
  over `D₊(s)`, units, and the normalization of stalk elements by fractions;
* `Stacks01n2TwistStalkNormalize`: the statement on a fixed chart
  `D₊(f s) ∋ y` (`twistPullbackHom_stalkMap_comp_tensorMap_bijective_of_mem_basicOpen`).
Here only the chart is chosen: `x = ρ y` is a relevant prime, so `x ∈ D₊(s)` for some homogeneous `s ∈ 𝒜 i`,
`i > 0` (`exists_mem_basicOpen`), i.e. `y ∈ D₊(f s) = ρ⁻¹ D₊(s)`.

## Natural-language proof (self-contained; the formalized route)

Notation. `x := ρ y = f⁻¹ y`. Sections of `O_A(n) = Proj.twist 𝒜 n` over `W` are functions `z ↦ s(z) ∈ A_{(z)}`
which are locally fractions `a/t` with `a ∈ 𝒜_{p}`, `t ∈ 𝒜_{q}`, `p = q + n`, `t ∉ z`; `O_B(n)` likewise.
`φ := twistToPushforward f hf n : O_A(n) ⟶ ρ_* O_B(n)` acts pointwise by the local ring map
`A_{(ρ z)} → B_{(z)}`, `a/t ↦ f a / f t`, and `θ` is its adjoint transpose. Two formulas describe `Θ_y` on pure
tensors: `T (b ⊗ m) = b • u_y m` (`modulePullbackStalkTensorMap_tmul`) and `θ_y (u_y (germ s)) = germ (φ s)`
(`moduleStalkMap_transpose_unit_germ`), hence `Θ_y (b ⊗ germ s) = b • germ (φ s)`.

Fix a homogeneous `s ∈ 𝒜_i`, `i > 0`, with `s ∉ x`; then `f s ∉ y`. Write `S := 𝒜_(s)`, `S' := ℬ_(f s)`
(Mathlib `Proj.awayToSection` identifies them with sections of `O` over `D₊(s)`, `D₊(f s)`),
`M₀ := (A_s)_n` (fractions `a / s^k`, `a ∈ 𝒜_{ki+n}`; `twistAway`), `M₀' := (B_{f s})_n`, with the section maps
`secA : M₀ → Γ(D₊(s), O_A(n))`, `secB : M₀' → Γ(D₊(f s), O_B(n))` (`twistSection`), and
`T₁ : R' ⊗_R M₀ → M₀'`, `r ⊗ m ↦ r • (f a / (f s)^k)` (`twistAwayLift`), which is **bijective**
(`twistAwayLift_bijective`: surjective by `pieceLift_surjective` in degree `ki+n`; injective by common
denominators and `pieceLift_injective`, exactly as for `awayLift_bijective`).

Normalization at the point (`i = deg s`): (a) every `μ ∈ O_A(n)_x` is `v • germ (secA m)` with `v ∈ O_{A,x}`,
`m ∈ M₀` (`a/t = (s^q/t^i) · (a t^{i-1}/s^q)`); (b) every `b ∈ O_{B,y}` satisfies `germ τ · b = germ σ` with
`τ, σ ∈ S'`, `germ τ` a unit (`c/d = (d^i/(f s)^q)⁻¹ · (c d^{i-1}/(f s)^q)`); (c) if `germ_y (secB m') = 0` then
`u • m' = 0` for some `u ∈ S'` with `germ u` a unit (evaluate at `y`, take a homogeneous component `t_q ∉ y` of an
annihilator `t`, `u := t_q^i / (f s)^q`).

Put `jHom : R' ⊗_R M₀ → O_{B,y} ⊗ O_A(n)_x`, `r ⊗ m ↦ r • (1 ⊗ germ (secA m))`. Then
(N2) `Θ_y (jHom ζ) = germ_y (secB (T₁ ζ))`; (N4) for `u ∈ S'`, `germ u • jHom ζ = jHom ζ'` with `T₁ ζ' = u • T₁ ζ`
(write `u = Σ r_l • Away.map (q_l)`, `awayLift_surjective`, and move `q_l` across the tensor); (N1) for every
`ξ` there is a unit `germ τ` with `germ τ • ξ = jHom ζ` (by (a), (b), (N4)).
**Surjective**: `ν = v • germ (secB m')` (a), `m' = T₁ ζ`, so `ν = Θ_y (v • jHom ζ)` (N2).
**Injective**: `Θ_y ξ = 0` ⇒ `germ_y (secB (T₁ ζ)) = 0` for `germ τ • ξ = jHom ζ` (N1, N2) ⇒ `u • T₁ ζ = 0` (c)
⇒ `T₁ ζ' = 0` (N4) ⇒ `ζ' = 0` ⇒ `germ u • jHom ζ = 0` ⇒ `jHom ζ = 0` ⇒ `ξ = 0`.

Edge cases: `Proj ℬ = ∅` (e.g. `R' = 0`): vacuous. `n = 0`: `O(0) = O`, the same route. `f s` a unit: harmless.

Source: Stacks 01N2 (last sentence: `O_{Proj B}(n) = ψ^* O_{Proj A}(n)` for `B = A ⊗_R R'`), via 01MX (θ);
the paper uses it only through Stacks 01N2/01NO.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory
open scoped AlgebraicGeometry HomogeneousIdeal

noncomputable section

/-- **Stacks 01N2 (last sentence) on stalks.** For `B = R' ⊗_R A` (graded), `ρ = Proj.map f hf` and
`θ = Proj.twistPullbackHom f hf n`, the composite of the pullback-stalk tensor map
`O_{B,y} ⊗_{O_{A,ρ y}} O_A(n)_{ρ y} → (ρ^* O_A(n))_y` with the stalk map `θ_y` is bijective for every `y`.
Proof: choose a chart `D₊(s) ∋ ρ y` (`exists_mem_basicOpen`) and apply the chart-level statement
`twistPullbackHom_stalkMap_comp_tensorMap_bijective_of_mem_basicOpen` (`Stacks01n2TwistStalkNormalize.lean`).
Complete natural-language proof in the module docstring. -/
theorem AlgebraicGeometry.Proj.twistPullbackHom_stalkMap_comp_tensorMap_bijective
    {R R' A B : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (fR : A →ₐ[R] B) (hfR : ∀ a, fR a = f a)
    (hbc : IsBaseChange R' fR.toLinearMap) (n : ℤ) (y : AlgebraicGeometry.Proj ℬ) :
    Function.Bijective
      (⇑(AlgebraicGeometry.Scheme.Modules.moduleStalkMap (AlgebraicGeometry.Proj ℬ) y
          (AlgebraicGeometry.Proj.twistPullbackHom f hf n)) ∘
        ⇑(AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap (AlgebraicGeometry.Proj.map f hf)
          (AlgebraicGeometry.Proj.twist 𝒜 n) y)) := by
  obtain ⟨i, s, hs, hi, hx⟩ := MiyaokaMori.Stacks01n2TwistStalk.exists_mem_basicOpen 𝒜
    ((AlgebraicGeometry.Proj.map f hf).base y)
  exact MiyaokaMori.Stacks01n2TwistStalk.twistPullbackHom_stalkMap_comp_tensorMap_bijective_of_mem_basicOpen
    𝒜 ℬ f hf fR hfR hs hi n y hx hbc

end
