import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial

/-! # The pullback of a section from the curve is the constant term of the `ξ`-expansion

A section `π^*s` pulled back along `Tot(L) → C̃` is the constant term of the `ξ`-expansion: `π^*s = s·ξ^0`
(`xiMonomial L M 0`, with the coefficient `s` viewed through `coefficientZeroIso⁻¹` as a section of `M^1 ⊗ L^0`).
Hence (with `xiCoefficient_xiMonomial`) the `0`-th `ξ`-coefficient of `π^*s` is `s` and all positive-order
coefficients vanish, which is the shape of the term `ρ^*f_ℓ` in equation (4.1) of
Lemma 4.1 of the paper.

The main theorem `sectionPullbackAlong_totalSpace_eq_xiMonomial_zero` follows in one line from the upstream lemma
`xiMonomial_zero_eq_sectionPullbackAlong` (`TotSectionsPolynomial.lean`), whose proof works entirely at the level
of morphisms (not on sections); the natural-language proof below is the proof of that upstream lemma.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- **`π^*s` is a monomial of degree `0`**: `sectionPullbackAlong π s = xiMonomial L M 0 (coefficientZeroIso⁻¹ s)`.

Source: the constant term `π_L^*(ρ^*f_ℓ)` of the expansion (4.1) of the paper.

## Proof (notation)
`π : Tot(L) → C̃` (`(totalSpace L.toModules).hom`), `S := Sym(L^∨) = symGradedAlgebra (dual L)`,
`Tot(L) = Spec_{C̃} S.total`, `σ := relativeSpec.structureHom S.total : S.total.carrier ⟶ π_*O_Tot` (an isomorphism,
`structureIso`), `θ := projectionFormulaHom π M O_Tot : M ⊗ π_*O_Tot ⟶ π_*(π^*M ⊗ O_Tot)`,
`τ := tensorIsoTensorObj M T_0`, `T_0 := moduleTensorPower (dual L) 0` (definitionally `𝟙_`),
`Θ_0 := totalSpace.tensorPowerToSymPart L 0 : T_0 ⟶ S_0`, `ι_0 := S.totalIncl 0 = Sigma.ι S.part 0`.

1. **Unfold the right-hand side** (all definitions):
   `xiMonomial L M 0 c = totalSpace.monomial L M 0 ((coefficientModuleIso L M 0).inv c)`;
   `monomial L M 0 c' = pushforwardSectionToPullback π M ((monomialHom L M 0) c')`;
   `monomialHom L M 0 = τ.hom ≫ (M ◁ (Θ_0 ≫ ι_0 ≫ σ))`; `pushforwardSectionToPullback π M y = (ρ_ (π^*M)).hom (θ y)`.
2. **The coefficient isomorphisms at `q = 0` compose to the inverse right unitor**:
   `coefficientZeroIso L M = τ' ≪≫ tensorIso zpowOneIso (refl) ≪≫ ρ_ M` (`τ' = tensorIsoTensorObj (M.zpow 1) (L.zpow 0)`),
   `coefficientModuleIso L M 0 = τ ≪≫ tensorIso zpowOneIso.symm (zpowNegIso 0).symm ≪≫ τ'.symm`, and
   `zpowNegIso 0 = Iso.refl`. Hence `(coefficientZeroIso).inv ≫ (coefficientModuleIso L M 0).inv ≫ τ.hom = (ρ_ M).inv`
   (`Iso.inv_hom_id`, `tensorHom_comp_tensorHom`, `tensorHom_id`), so the right-hand side is
   `(ρ_ π^*M).hom (θ ((M ◁ (Θ_0 ≫ ι_0 ≫ σ)) ((ρ_ M).inv s)))`, i.e. "`s ⊗ 1` through `θ`, then drop `⊗ O`".
3. **The degree-`0` part is the algebra unit**: `Θ_0 ≫ ι_0 ≫ σ = η_π`, where `η_π : 𝟙_ ⟶ π_*O_Tot` is the unit of
   `π_*O_Tot` (the map `O_{C̃} → π_*O_Tot` given by `π^♯`). Indeed `σ` is an algebra map (the structure map of the
   relative Spec; `structureHom_app_apply` gives its formula on sections) and sends the unit `S.one ≫ Sigma.ι S.part 0`
   of `S.total` to the unit of `π_*O_Tot`, while `Θ_0 = powIso_0.inv ≫ symPowπ (dual L) 0` with `powIso_0 = refl` and
   `symPowπ V 0 : 𝟙_ ⟶ Sym^0 V` the unit `S.one` of `Sym` (`tensorPowerToSymPart_zero`,
   `relativeSpec.one_comp_structureHom`).
4. **The projection formula on `s ⊗ 1`**: `θ = homEquiv (pullbackTensorObjHom π M (π_*O) ≫ (π^*M ◁ counit))`, so on
   sections `θ(x)` is `π_*(…)` applied to the adjunction unit `unit_{M ⊗ π_*O}(x)`. For `x = (M ◁ η_π)((ρ_ M).inv s)`
   (`= s ⊗ 1`): the unit is natural, `pullbackTensorObjHom` is natural in the second variable, and
   `counit ∘ π^*η_π = 𝟙_{O_Tot}` (triangle identity), so `θ(s ⊗ 1) = (π^*s) ⊗ 1` with `π^*s = sectionPullbackAlong π s`.
   The formal proof does this at the level of morphisms with the abstract lemma
   `whiskerLeft_homEquiv_η_projFormulaHom_unit` (adjoint transpose, `δ_natural_right`, oplax right unitality).
5. Conclude with `(ρ_ M).inv ≫ (ρ_ M).hom = 𝟙` and take sections over `⊤` (`rfl`). ∎

Edge cases: for `s = 0` both sides are `0` (both are images under morphisms of sheaves of modules); `κ` does not
occur; `L`, `M` are arbitrary line bundles. -/
theorem sectionPullbackAlong_totalSpace_eq_xiMonomial_zero {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety)
    (s : (M.toModules.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom s
      = xiMonomial L M 0 (((coefficientZeroIso L M).inv.val.app (Opposite.op ⊤)).hom s) := by
  rw [xiMonomial_zero_eq_sectionPullbackAlong, AlgebraicGeometry.Scheme.Modules.app_top_inv_hom]

end
