import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafAsCokernel
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafLocal
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalSectionToFunctionField
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheaf
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.SheafOfUnits
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeilUniqueHelpers

/-! # Local equations of a Cartier divisor

Every Cartier divisor `D ∈ CDiv(X)` is given by local equations: a family `{(U_i, f_i)}` with the
`U_i` covering `X`, `f_i ∈ K(X)^×`, and `f_i / f_j` a unit on `U_i ∩ U_j`, such that
`D = CartierDivisor.ofLocalData U f`.

Proof sketch: the quotient map `𝒦^* → 𝒦^*/O^*` is locally surjective (`quotientπ_exists_local`),
so every point `x` has a neighbourhood `U_x` with a local lift `t_x`; let `f_x` be the value of
`t_x` at the generic point. On `U_x ∩ U_y` both `t_x` and `t_y` lift `D`, so their ratio is
stalkwise a unit of `O^*` (`local_unit_ratio_eq`). Finally `ofLocalData` is chosen by the property
"restricts on every `U_i` to the class of a section with value `f_i`"; `D` has this property, and a
global section with this property is unique (injectivity in Stacks 01X5 gives uniqueness of the
section with value `f_i`, then separatedness of the quotient sheaf).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Every Cartier divisor is glued from compatible local equations. -/
theorem cartierDivisor_exists_localData {k : Type u} [Field k] (X : Variety k)
    (D : CartierDivisor X) :
    ∃ (ι : Type u) (U : ι → X.toScheme.Opens) (f : ι → (X.toScheme.functionField)ˣ),
      CartierDivisor.IsLocalData U f ∧ D = CartierDivisor.ofLocalData U f := by
  classical
  let I := AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme
  let Q := TopCat.Sheaf.quotient I
  let π := TopCat.Sheaf.quotientπ I
  have hloc : ∀ x : X.toScheme, ∃ (U : X.toScheme.Opens) (_ : x ∈ U)
      (t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)),
      Q.val.map (homOfLE (show U ≤ ⊤ from le_top)).op (Additive.toMul D) = π.hom.app (op U) t := by
    intro x
    obtain ⟨U, hxU, hU, t, ht⟩ := TopCat.Sheaf.quotientπ_exists_local I ⊤ (Additive.toMul D) x trivial
    exact ⟨U, hxU, t, ht⟩
  choose U hxU t ht using hloc
  have hne : ∀ x, Nonempty (U x) := fun x => ⟨⟨x, hxU x⟩⟩
  let f : X.toScheme → (X.toScheme.functionField)ˣ := fun x =>
    @AlgebraicGeometry.Scheme.rationalUnitsSectionToFunctionField X.toScheme _ (U x) (hne x) (t x)
  have hcover : (⨆ x, U x) = ⊤ :=
    top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
  -- the restricted lifts are still local equations
  have hres : ∀ (x : X.toScheme) (W : X.toScheme.Opens) (hW : W ≤ U x),
      Q.val.map (homOfLE (show W ≤ ⊤ from le_top)).op (Additive.toMul D) =
        π.hom.app (op W) (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hW).op (t x)) := by
    intro x W hW
    have heq : Q.val.map (homOfLE (show W ≤ ⊤ from le_top)).op =
        Q.val.map (homOfLE (show U x ≤ ⊤ from le_top)).op ≫ Q.val.map (homOfLE hW).op := by
      rw [← Functor.map_comp]; rfl
    have h1 := congrArg (fun q => q.hom (Additive.toMul D)) heq
    have hn := congrArg (fun z => z (t x)) (π.hom.naturality (homOfLE hW).op)
    exact h1.trans ((congrArg (Q.val.map (homOfLE hW).op) (ht x)).trans hn.symm)
  have hratio : ∀ x y : X.toScheme, ∀ z ∈ U x ⊓ U y,
      ((f x / f y : (X.toScheme.functionField)ˣ) : X.toScheme.functionField) ∈
        Set.range (fun v : (X.toScheme.presheaf.stalk z)ˣ =>
          algebraMap (X.toScheme.presheaf.stalk z) X.toScheme.functionField v) := by
    intro x y z hz
    have hW : Nonempty (U x ⊓ U y : X.toScheme.Opens) := ⟨⟨z, hz⟩⟩
    have := hne x
    have := hne y
    obtain ⟨W', hW'W, hzW', a, ha⟩ :=
      CartierToWeilQuotientUnitRatio.local_unit_ratio_eq (V := X) hW z hz
        (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE inf_le_left).op (t x))
        (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE inf_le_right).op (t y))
        ((hres x _ inf_le_left).symm.trans (hres y _ inf_le_right))
    rw [X.toScheme.rationalUnitsSectionToFunctionField_res (U x) _ inf_le_left,
      X.toScheme.rationalUnitsSectionToFunctionField_res (U y) _ inf_le_right] at ha
    refine ⟨a, ha.trans ?_⟩
    simp [f, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  have hUf : CartierDivisor.IsLocalData U f :=
    ⟨hcover, fun x y z hz => ⟨hratio x y z hz, hratio y x z ⟨hz.2, hz.1⟩⟩⟩
  refine ⟨X.toScheme, U, f, hUf, ?_⟩
  let P : Q.val.obj (op ⊤) → Prop := fun s =>
    ∀ i, ∀ hne' : Nonempty (U i),
      ∃ t' : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op (U i)),
        (haveI := hne'; X.toScheme.rationalUnitsSectionToFunctionField (U i) t') = f i ∧
        Q.val.map (homOfLE (show U i ≤ ⊤ from le_top)).op s = π.hom.app (op (U i)) t'
  have hPD : P (Additive.toMul D) := fun i _ => ⟨t i, rfl, ht i⟩
  have hPε : P (Classical.epsilon P) := Classical.epsilon_spec ⟨_, hPD⟩
  have hrepr : Additive.toMul (CartierDivisor.ofLocalData U f) = Classical.epsilon P := by
    unfold CartierDivisor.ofLocalData
    dsimp
    change Additive.toMul (if CartierDivisor.IsLocalData U f then
      Additive.ofMul (Classical.epsilon P) else 0) = Classical.epsilon P
    rw [if_pos hUf]
    rfl
  have huniq : Additive.toMul D = Classical.epsilon P := by
    apply Q.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) (by rw [hcover])
    intro i
    obtain ⟨t', ht'v, ht'q⟩ := hPε i (hne i)
    have := hne i
    have htt : t' = t i :=
      X.toScheme.rationalUnitsSectionToFunctionField_injective (U i) ht'v
    exact (ht i).trans ((congrArg (π.hom.app (op (U i))) htt.symm).trans ht'q.symm)
  exact congrArg Additive.ofMul (huniq.trans hrepr.symm)


end
