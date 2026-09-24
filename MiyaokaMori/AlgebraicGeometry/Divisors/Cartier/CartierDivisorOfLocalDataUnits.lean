import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafStalk
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeilUniqueHelpers

/-! # Local equations that are units glue to the zero divisor

If `{(U_i, f_i)}` are Cartier local data and every `f_i` is, at every point of `U_i`, the image of a
unit of `O_{X,x}`, then `CartierDivisor.ofLocalData U f = 0`.

Source: Hartshorne II.6.11, first paragraph of the proof (`f_i ∈ Γ(U_i, O^*)` implies `D = 0`,
p. 141); this is the definition of the quotient sheaf `𝒦^*/O^*`: sections of `O^*` become `1`.

Proof sketch: `ofLocalData U f` restricts on `U_i` to `π(t_i)` for a section `t_i ∈ 𝒦^*(U_i)` with
value `f_i` (`CartierToWeilLocalSection.local_section_ofLocalData`). Since `f_i` is stalkwise a
unit, it is the germ of a unit section `s_i ∈ Γ(U_i, O)^×`
(`AlgebraicGeometry.Scheme.exists_unit_section_of_stalkwise_unit`); `ι(s_i) ∈ 𝒦^*(U_i)` has the same value as
`t_i`, and evaluation is injective (`rationalUnitsSectionToFunctionField_injective`), so
`t_i = ι(s_i)`, while `π ∘ ι = 1` (`TopCat.Sheaf.comp_quotientπ_hom_app_apply`). The `U_i` cover
`X`, so separatedness of the sheaf gives that the global section is `1`. For `U_i = ∅` the section
group is trivial.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CartierDivisor

variable {k : Type u} [Field k] {X : Variety k}

/-- The value of `ι(u) ∈ 𝒦^*(U)` is the germ of `u` in the function field, where
`ι = unitsSheafToRationalFunctionsUnits` and the value is `germToFunctionField`. -/
theorem val_rationalUnitsSectionToFunctionField_unitsSheafToRationalFunctionsUnits
    {U : X.toScheme.Opens} [Nonempty U] (u : (Γ(X.toScheme, U))ˣ) :
    ((X.toScheme.rationalUnitsSectionToFunctionField U
        ((AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme).hom.app (op U) u) :
      (X.toScheme.functionField)ˣ) : X.toScheme.functionField) =
      X.toScheme.germToFunctionField U (u : Γ(X.toScheme, U)) := by
  change (X.toScheme.rationalSectionToFunctionField U).hom
    ((X.toScheme.toRationalFunctionsSheaf.hom.app (op U)).hom (u : Γ(X.toScheme, U))) = _
  exact ConcreteCategory.congr_hom
    (X.toScheme.toRationalFunctionsSheaf_rationalSectionToFunctionField U) (u : Γ(X.toScheme, U))

/-- Local equations that are stalkwise units glue to the zero Cartier divisor. -/
theorem ofLocalData_eq_zero_of_forall_units {ι : Type u}
    (U : ι → X.toScheme.Opens) (f : ι → (X.toScheme.functionField)ˣ) (hUf : IsLocalData U f)
    (h : ∀ i, ∀ x ∈ U i, ∃ v : (X.toScheme.presheaf.stalk x)ˣ,
      algebraMap (X.toScheme.presheaf.stalk x) X.toScheme.functionField v =
        (f i : X.toScheme.functionField)) :
    ofLocalData U f = 0 := by
  let I := AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme
  let Q := TopCat.Sheaf.quotient I
  let π := TopCat.Sheaf.quotientπ I
  have key : Additive.toMul (ofLocalData U f) = (1 : Q.val.obj (op ⊤)) := by
    apply Q.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) (by rw [hUf.1])
    intro i
    by_cases hne : Nonempty (U i)
    · obtain ⟨⟨x, hx⟩⟩ := hne
      have : Nonempty (U i) := ⟨⟨x, hx⟩⟩
      obtain ⟨t, ht, hq⟩ := CartierToWeilLocalSection.local_section_ofLocalData U f hUf x i hx
      rw [map_one]
      change Q.val.map (homOfLE (show U i ≤ ⊤ from le_top)).op (Additive.toMul (ofLocalData U f)) = 1
      rw [hq]
      obtain ⟨s, hs⟩ := AlgebraicGeometry.Scheme.exists_unit_section_of_stalkwise_unit X.toScheme (U i)
        (f i : X.toScheme.functionField) (fun y => h i y.1 y.2)
      have htu : t = I.hom.app (op (U i)) s := by
        apply X.toScheme.rationalUnitsSectionToFunctionField_injective (U i)
        rw [ht]
        apply Units.ext
        rw [val_rationalUnitsSectionToFunctionField_unitsSheafToRationalFunctionsUnits]
        exact hs.symm
      rw [htu]
      exact TopCat.Sheaf.comp_quotientπ_hom_app_apply I (op (U i)) s
    · have hbot : U i = ⊥ := by
        apply le_antisymm _ bot_le
        intro x hx
        exact (hne ⟨⟨x, hx⟩⟩).elim
      have hterm := Q.isTerminalOfEqEmpty hbot
      have hzero : IsZero (Q.obj.obj (op (U i))) :=
        IsZero.of_iso (isZero_zero CommGrpCat.{u})
          (hterm.uniqueUpToIso (isZero_zero CommGrpCat.{u}).isTerminal)
      have : Subsingleton (Q.val.obj (op (U i))) := CommGrpCat.subsingleton_of_isZero hzero
      exact Subsingleton.elim _ _
  exact Additive.toMul.injective key

end CartierDivisor

end
