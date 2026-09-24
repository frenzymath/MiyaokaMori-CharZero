import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.FiberDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.CurveStalkFunctionField

/-! # Pullback of Cartier local data along a dominant morphism; local equations of a fibre divisor

Pulling back local equations `(U_i, g_i) ↦ (f⁻¹U_i, f^♮ g_i)` along a dominant morphism
`f : X → Y` gives again local equation data: the covering condition follows from
`f⁻¹(⋃ U_i) = ⋃ f⁻¹U_i`; for compatibility, if `x ∈ f⁻¹U_i ∩ f⁻¹U_j` then `g_i / g_j = v` is a unit
of `O_{Y,f(x)}` and `f^♮(g_i / g_j) = f^♯_x(v)` is a unit of `O_{X,x}`
(`dominantFunctionFieldMap_algebraMap`). The file also gives explicit local equations of the fibre
divisor: there are local equations `(U_i, g_i)` of the point divisor `[y]` with
`π^*[y] = ofLocalData (π⁻¹U_i, π^♮ g_i)`. This is used for the fibre decomposition in Lemma 5.1 of the paper; see Hartshorne II.6 for the pullback of Cartier divisors.

`CartierDivisor.isLocalData_pullback_of_isDominant` is an alias of
`CartierDivisor.IsLocalData.pullback` (in
`MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback`), kept for its existing
users; new code should use `CartierDivisor.IsLocalData.pullback`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The pullback of local equation data along a dominant morphism is again local equation data
(alias of `CartierDivisor.IsLocalData.pullback`). -/
theorem CartierDivisor.isLocalData_pullback_of_isDominant {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsDominant f]
    {ι : Type u} (U : ι → Y.toScheme.Opens) (g : ι → (Y.toScheme.functionField)ˣ)
    (hUg : CartierDivisor.IsLocalData U g) :
    CartierDivisor.IsLocalData (fun i => f ⁻¹ᵁ U i)
      (fun i => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (g i)) :=
  CartierDivisor.IsLocalData.pullback f hUg

/-- Explicit local equations of the fibre divisor: there are local equations `(U_i, g_i)`
(compatible, gluing to `[y]`) with `π^*[y] = ofLocalData (π⁻¹U_i, π^♮ g_i)`
(`CartierDivisor.pullback_ofLocalData`: the pullback does not depend on the choice of local data). -/
theorem fiberDivisor_eq_ofLocalData {k : Type u} [Field k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme)
    (hπ : AlgebraicGeometry.Surjective π) [AlgebraicGeometry.IsDominant π] (y : C.toScheme) :
    ∃ (ι : Type u) (U : ι → C.toScheme.Opens) (g : ι → (C.toScheme.functionField)ˣ),
      CartierDivisor.IsLocalData (X := C.toVariety) U g ∧
      Divisor.ofPoint y = CartierDivisor.ofLocalData (X := C.toVariety) U g ∧
      fiberDivisor π hπ y = CartierDivisor.ofLocalData (X := S.toVariety) (fun i => π ⁻¹ᵁ U i)
        (fun i => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap π).hom.toMonoidHom (g i)) := by
  obtain ⟨ι, U, g, h1, h2⟩ := cartierDivisor_exists_localData C.toVariety (Divisor.ofPoint y)
  refine ⟨ι, U, g, h1, h2, ?_⟩
  show CartierDivisor.pullback π hπ.surj (Divisor.ofPoint y) = _
  rw [h2]
  exact CartierDivisor.pullback_ofLocalData (X := S.toVariety) (Y := C.toVariety) π hπ.surj h1

end
