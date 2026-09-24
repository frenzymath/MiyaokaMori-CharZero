import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafAsCokernel
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheaf
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafSheafify
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalSectionToFunctionField
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.SheafOfUnits
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.SheafOfUnitsPostcompose
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety

/-! # Cartier divisors

The group of Cartier divisors `CDiv(X) = Γ(X, 𝒦_X^*/O_X^*)` of a variety `X`: the global sections
of the quotient of the sheaf of units of the sheaf of rational functions by the sheaf of units of
the structure sheaf, written additively. Local equations `{(U_i, f_i)}` with stalkwise unit ratios
glue to a Cartier divisor (`CartierDivisor.ofLocalData`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The map `O_X^* → 𝒦_X^*` of sheaves of units induced by the structure map `O_X → 𝒦_X`. -/

noncomputable def AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits
    (X : AlgebraicGeometry.Scheme.{u}) : X.unitsSheaf ⟶ X.rationalFunctionsUnitsSheaf :=
  TopCat.Sheaf.unitsMap X.toRationalFunctionsSheaf

/-- The group of Cartier divisors `CDiv(X) = Γ(X, 𝒦_X^*/O_X^*)`, the multiplicative group written
additively. -/

def CartierDivisor {k : Type u} [Field k] (X : Variety k) : Type u :=
  Additive ((TopCat.Sheaf.quotient
    (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.obj (Opposite.op ⊤))

instance {k : Type u} [Field k] (X : Variety k) : AddCommGroup (CartierDivisor X) :=
  inferInstanceAs (AddCommGroup (Additive ((TopCat.Sheaf.quotient
    (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.obj (Opposite.op ⊤))))

/-- Compatibility of local equation data, in stalkwise form (no nonemptiness of overlaps is needed):
the `U_i` cover `X`, and at every point `x ∈ U_i ∩ U_j` both `f_i / f_j` and `f_j / f_i` are images of
units of `O_{X,x}`. -/

def CartierDivisor.IsLocalData {k : Type u} [Field k] {X : Variety k} {ι : Type u}
    (U : ι → X.toScheme.Opens) (f : ι → (X.toScheme.functionField)ˣ) : Prop :=
  (⨆ i, U i) = ⊤ ∧ ∀ i j, ∀ x ∈ U i ⊓ U j,
    ((f i / f j : (X.toScheme.functionField)ˣ) : X.toScheme.functionField) ∈
      Set.range (fun v : (X.toScheme.presheaf.stalk x)ˣ =>
        algebraMap (X.toScheme.presheaf.stalk x) X.toScheme.functionField v) ∧
    ((f j / f i : (X.toScheme.functionField)ˣ) : X.toScheme.functionField) ∈
      Set.range (fun v : (X.toScheme.presheaf.stalk x)ˣ =>
        algebraMap (X.toScheme.presheaf.stalk x) X.toScheme.functionField v)

/-- The Cartier divisor glued from local equations; `0` when the data are not compatible.
The class `[f_i] ∈ (𝒦^*/O^*)(U_i)` is `π(t)` for a section `t ∈ 𝒦^*(U_i)` whose value at the
generic point is `f_i` (the evaluation map `rationalUnitsSectionToFunctionField` is restriction to
the generic point). The global section is the one restricting on every nonempty `U_i` to such a
`[f_i]`; for compatible data it exists and is unique by Stacks 01X5 and the sheaf condition. -/

noncomputable def CartierDivisor.ofLocalData {k : Type u} [Field k] {X : Variety k} {ι : Type u}
    (U : ι → X.toScheme.Opens) (f : ι → (X.toScheme.functionField)ˣ) : CartierDivisor X :=
  let Q := TopCat.Sheaf.quotient (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)
  let π := TopCat.Sheaf.quotientπ (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)
  open Classical in
  if CartierDivisor.IsLocalData U f then
    Additive.ofMul (Classical.epsilon fun s : Q.val.obj (Opposite.op ⊤) =>
      ∀ i, ∀ hne : Nonempty (U i),
        ∃ t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (Opposite.op (U i)),
          (haveI := hne; X.toScheme.rationalUnitsSectionToFunctionField (U i) t) = f i ∧
          Q.val.map (homOfLE le_top : U i ⟶ ⊤).op s = π.hom.app (Opposite.op (U i)) t)
  else 0

end
