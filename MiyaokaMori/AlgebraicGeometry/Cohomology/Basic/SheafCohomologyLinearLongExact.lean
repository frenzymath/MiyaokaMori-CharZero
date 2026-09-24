import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLes
import MiyaokaMori.CategoryTheory.ExtPostcompLinear
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap

/-! # The linear long exact sequence of sheaf cohomology

Let `X` be a scheme and `0 → M' → M → M'' → 0` a short exact sequence of `O_X`-modules. There is a
`Γ(X, O_X)`-linear connecting map `δ : H^n(X, M'') → H^{n+1}(X, M')`, and the long sequence
`H^n(M') → H^n(M) → H^n(M'') → H^{n+1}(M') → H^{n+1}(M)` satisfies `LinearMap.range = LinearMap.ker`
at every place; when `X` is a `K`-scheme the same holds for the `K`-linear maps. Corollaries: if
`H^n(M'') = 0` and `H^{n+1}(M'') = 0`, adjacent terms are `K`-linearly isomorphic and have equal
dimension; if `H^{n+1}(M') = 0`, then `H^n(M) → H^n(M'')` is surjective.

Proof sketch:
1. The forgetful functor to abelian sheaves sends the short exact sequence of modules to a short
   exact sequence of abelian sheaves (`bridge_shortExact_toSheaf`).
2. The action `μ_r` of a scalar `r` on the three terms commutes with `S.f`, `S.g`
   (`smulEnd_naturality`); postcomposition with the extension class is `Γ(X, O_X)`-linear, and
   `range = ker` holds at the three places (`Ext.postcompLinear`).
3. The `K`-structure is restriction of scalars along `K → Γ(X, O_X)`, so a `Γ(X, O_X)`-linear map is
   `K`-linear, and `range`, `ker` are unchanged as sets.
4. The corollaries are linear algebra: `ker = range(from 0) = ⊥` gives injectivity,
   `range = ker(to 0) = ⊤` gives surjectivity.

Source: Stacks 01E0; Mathlib `Ext.covariant_sequence_exact₁/₂/₃`. This is the `K`-linear version of
`sheafCohomology_long_exact`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The underlying short complex of abelian sheaves of a short complex of modules. -/
abbrev Scheme.Modules.toAddCommGrpSheafShortComplex (S : ShortComplex X.Modules) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (Scheme.Modules.toAddCommGrpSheafMap S.f) (Scheme.Modules.toAddCommGrpSheafMap S.g)
    (by
      rw [← Scheme.Modules.toAddCommGrpSheafMap_comp, S.zero]
      exact (SheafOfModules.toSheaf X.ringCatSheaf).map_zero _ _)

theorem Scheme.Modules.shortExact_toAddCommGrpSheaf {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (Scheme.Modules.toAddCommGrpSheafShortComplex S).ShortExact :=
  bridge_shortExact_toSheaf (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf) S.f S.g S.zero) hS

/- Implementation note: as in `SheafCohomologyLinearMap.lean`, the map is produced by an existence
   theorem plus `Classical.choose`, so that the kernel crosses between the `sheafCohomology` and the
   `Ext` spelling only inside the proof of one theorem. -/

theorem sheafCohomology.exists_δ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : sheafCohomology X S.X₃ n₀ →ₗ[Γ(X, ⊤)] sheafCohomology X S.X₁ n₁,
      (∀ x : sheafCohomology X S.X₃ n₀,
        δ x = Abelian.Ext.comp (x : Sheaf.H S.X₃.toAddCommGrpSheaf n₀)
          (Scheme.Modules.shortExact_toAddCommGrpSheaf hS).extClass h) ∧
      LinearMap.range (sheafCohomology.map S.f n₀) = LinearMap.ker (sheafCohomology.map S.g n₀) ∧
      LinearMap.range (sheafCohomology.map S.g n₀) = LinearMap.ker δ ∧
      LinearMap.range δ = LinearMap.ker (sheafCohomology.map S.f n₁) := by
  have hS' := Scheme.Modules.shortExact_toAddCommGrpSheaf hS
  have ef : ∀ n, sheafCohomology.map S.f n =
      Abelian.Ext.postcompLinear S.X₁.smulEnd S.X₂.smulEnd (Scheme.Modules.smul_sheafH n)
        (Scheme.Modules.smul_sheafH n) (Scheme.Modules.toAddCommGrpSheafShortComplex S).f
        (Scheme.Modules.smulEnd_naturality S.f) :=
    fun n => LinearMap.ext fun x => sheafCohomology.map_apply S.f n x
  have eg : ∀ n, sheafCohomology.map S.g n =
      Abelian.Ext.postcompLinear S.X₂.smulEnd S.X₃.smulEnd (Scheme.Modules.smul_sheafH n)
        (Scheme.Modules.smul_sheafH n) (Scheme.Modules.toAddCommGrpSheafShortComplex S).g
        (Scheme.Modules.smulEnd_naturality S.g) :=
    fun n => LinearMap.ext fun x => sheafCohomology.map_apply S.g n x
  refine ⟨Abelian.Ext.extClassLinear hS' h S.X₁.smulEnd S.X₂.smulEnd S.X₃.smulEnd
    (Scheme.Modules.smul_sheafH n₀) (Scheme.Modules.smul_sheafH n₁)
    (Scheme.Modules.smulEnd_naturality S.f) (Scheme.Modules.smulEnd_naturality S.g),
    fun _ => rfl, ?_, ?_, ?_⟩
  · rw [ef, eg]
    exact Abelian.Ext.range_postcompLinear_f_eq_ker_g hS' _ _ _ _ _ _ _ _
  · rw [eg]
    exact Abelian.Ext.range_postcompLinear_g_eq_ker_extClassLinear hS' h _ _ _ _ _ _ _ _
  · rw [ef]
    exact Abelian.Ext.range_extClassLinear_eq_ker_postcompLinear_f hS' h _ _ _ _ _ _ _ _

section LongExact

variable {S : ShortComplex X.Modules} (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

/-- The connecting map `δ : H^{n₀}(X, M'') → H^{n₁}(X, M')`, `Γ(X, O_X)`-linear. -/
def sheafCohomology.δ : sheafCohomology X S.X₃ n₀ →ₗ[Γ(X, ⊤)] sheafCohomology X S.X₁ n₁ :=
  Classical.choose (sheafCohomology.exists_δ hS n₀ n₁ h)

/-- Unfolding: `δ` is postcomposition with the extension class of the underlying short exact
sequence of abelian sheaves (Mathlib's connecting map). -/
theorem sheafCohomology.δ_apply (x : sheafCohomology X S.X₃ n₀) :
    sheafCohomology.δ hS n₀ n₁ h x =
      Abelian.Ext.comp (x : Sheaf.H S.X₃.toAddCommGrpSheaf n₀)
        (Scheme.Modules.shortExact_toAddCommGrpSheaf hS).extClass h :=
  (Classical.choose_spec (sheafCohomology.exists_δ hS n₀ n₁ h)).1 x

include hS in
/-- Exactness at `H^n(X, M)`. -/
theorem sheafCohomology.range_map_f_eq_ker_map_g (n : ℕ) :
    LinearMap.range (sheafCohomology.map S.f n) = LinearMap.ker (sheafCohomology.map S.g n) :=
  (Classical.choose_spec (sheafCohomology.exists_δ hS n (n + 1) rfl)).2.1

/-- Exactness at `H^{n₀}(X, M'')`. -/
theorem sheafCohomology.range_map_g_eq_ker_δ :
    LinearMap.range (sheafCohomology.map S.g n₀) = LinearMap.ker (sheafCohomology.δ hS n₀ n₁ h) :=
  (Classical.choose_spec (sheafCohomology.exists_δ hS n₀ n₁ h)).2.2.1

/-- Exactness at `H^{n₁}(X, M')`. -/
theorem sheafCohomology.range_δ_eq_ker_map_f :
    LinearMap.range (sheafCohomology.δ hS n₀ n₁ h) = LinearMap.ker (sheafCohomology.map S.f n₁) :=
  (Classical.choose_spec (sheafCohomology.exists_δ hS n₀ n₁ h)).2.2.2

/-! ### The `K`-linear version -/

section OverField

variable (K : Type u) [CommRing K] [X.Over (Spec (CommRingCat.of K))]

/-- The `K`-linear connecting map on a `K`-scheme. -/
def sheafCohomology.δOver : sheafCohomology X S.X₃ n₀ →ₗ[K] sheafCohomology X S.X₁ n₁ where
  toFun := sheafCohomology.δ hS n₀ n₁ h
  map_add' := _root_.map_add _
  map_smul' _ x := (sheafCohomology.δ hS n₀ n₁ h).map_smul _ x

@[simp]
theorem sheafCohomology.δOver_apply (x : sheafCohomology X S.X₃ n₀) :
    sheafCohomology.δOver hS n₀ n₁ h K x = sheafCohomology.δ hS n₀ n₁ h x := rfl

include hS in
/-- Exactness of the `K`-linear long exact sequence at `H^n(X, M)`. -/
theorem sheafCohomology.range_mapOver_f_eq_ker_mapOver_g (n : ℕ) :
    LinearMap.range (sheafCohomology.mapOver K S.f n) =
      LinearMap.ker (sheafCohomology.mapOver K S.g n) := by
  ext x
  have := SetLike.ext_iff.mp (sheafCohomology.range_map_f_eq_ker_map_g hS n) x
  simpa only [LinearMap.mem_range, LinearMap.mem_ker, sheafCohomology.mapOver_apply] using this

/-- Exactness of the `K`-linear long exact sequence at `H^{n₀}(X, M'')`. -/
theorem sheafCohomology.range_mapOver_g_eq_ker_δOver :
    LinearMap.range (sheafCohomology.mapOver K S.g n₀) =
      LinearMap.ker (sheafCohomology.δOver hS n₀ n₁ h K) := by
  ext x
  have := SetLike.ext_iff.mp (sheafCohomology.range_map_g_eq_ker_δ hS n₀ n₁ h) x
  simpa only [LinearMap.mem_range, LinearMap.mem_ker, sheafCohomology.mapOver_apply,
    sheafCohomology.δOver_apply] using this

/-- Exactness of the `K`-linear long exact sequence at `H^{n₁}(X, M')`. -/
theorem sheafCohomology.range_δOver_eq_ker_mapOver_f :
    LinearMap.range (sheafCohomology.δOver hS n₀ n₁ h K) =
      LinearMap.ker (sheafCohomology.mapOver K S.f n₁) := by
  ext x
  have := SetLike.ext_iff.mp (sheafCohomology.range_δ_eq_ker_map_f hS n₀ n₁ h) x
  simpa only [LinearMap.mem_range, LinearMap.mem_ker, sheafCohomology.mapOver_apply,
    sheafCohomology.δOver_apply] using this

end OverField

/-! ### Standard corollaries (vanishing ⇒ injective / surjective / isomorphism) -/

include hS in
/-- `H^n(M'') = 0` ⇒ `H^n(M') → H^n(M)` is surjective. -/
theorem sheafCohomology.map_f_surjective_of_subsingleton (n : ℕ)
    [Subsingleton (sheafCohomology X S.X₃ n)] :
    Function.Surjective (sheafCohomology.map S.f n) := by
  rw [← LinearMap.range_eq_top, sheafCohomology.range_map_f_eq_ker_map_g hS n,
    LinearMap.ker_eq_top]
  exact LinearMap.ext fun x => Subsingleton.elim _ _

include hS h in
/-- `H^{n₀}(M'') = 0` ⇒ `H^{n₁}(M') → H^{n₁}(M)` is injective. -/
theorem sheafCohomology.map_f_injective_of_subsingleton
    [Subsingleton (sheafCohomology X S.X₃ n₀)] :
    Function.Injective (sheafCohomology.map S.f n₁) := by
  rw [← LinearMap.ker_eq_bot, ← sheafCohomology.range_δ_eq_ker_map_f hS n₀ n₁ h,
    LinearMap.range_eq_bot]
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]

include hS h in
/-- `H^{n₁}(M') → H^{n₁}(M)` injective ⇒ `H^{n₀}(M) → H^{n₀}(M'')` surjective (an isomorphism on
`H^1` lets sections lift). -/
theorem sheafCohomology.map_g_surjective_of_map_f_injective
    (hf : Function.Injective (sheafCohomology.map S.f n₁)) :
    Function.Surjective (sheafCohomology.map S.g n₀) := by
  rw [← LinearMap.range_eq_top, sheafCohomology.range_map_g_eq_ker_δ hS n₀ n₁ h,
    LinearMap.ker_eq_top]
  have hδ : LinearMap.range (sheafCohomology.δ hS n₀ n₁ h) = ⊥ := by
    rw [sheafCohomology.range_δ_eq_ker_map_f hS n₀ n₁ h]
    exact LinearMap.ker_eq_bot.mpr hf
  exact LinearMap.range_eq_bot.mp hδ

include hS h in
/-- `H^{n₁}(M') = 0` ⇒ `H^{n₀}(M) → H^{n₀}(M'')` is surjective. -/
theorem sheafCohomology.map_g_surjective_of_subsingleton
    [Subsingleton (sheafCohomology X S.X₁ n₁)] :
    Function.Surjective (sheafCohomology.map S.g n₀) :=
  sheafCohomology.map_g_surjective_of_map_f_injective hS n₀ n₁ h
    (fun _ _ _ => Subsingleton.elim _ _)

include hS in
/-- `H^n(M') = 0` ⇒ `H^n(M) → H^n(M'')` is injective. -/
theorem sheafCohomology.map_g_injective_of_subsingleton (n : ℕ)
    [Subsingleton (sheafCohomology X S.X₁ n)] :
    Function.Injective (sheafCohomology.map S.g n) := by
  rw [← LinearMap.ker_eq_bot, ← sheafCohomology.range_map_f_eq_ker_map_g hS n,
    LinearMap.range_eq_bot]
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- `H^{n₀}(M'') = H^{n₁}(M'') = 0` ⇒ `H^{n₁}(M') ≃ₗ[K] H^{n₁}(M)`. -/
def sheafCohomology.equivOfSubsingletonRight (K : Type u) [CommRing K]
    [X.Over (Spec (CommRingCat.of K))]
    [Subsingleton (sheafCohomology X S.X₃ n₀)] [Subsingleton (sheafCohomology X S.X₃ n₁)] :
    sheafCohomology X S.X₁ n₁ ≃ₗ[K] sheafCohomology X S.X₂ n₁ :=
  LinearEquiv.ofBijective (sheafCohomology.mapOver K S.f n₁)
    ⟨sheafCohomology.map_f_injective_of_subsingleton hS n₀ n₁ h,
      sheafCohomology.map_f_surjective_of_subsingleton hS n₁⟩

/-- `H^{n₀}(M') = H^{n₁}(M') = 0` ⇒ `H^{n₀}(M) ≃ₗ[K] H^{n₀}(M'')`. -/
def sheafCohomology.equivOfSubsingletonLeft (K : Type u) [CommRing K]
    [X.Over (Spec (CommRingCat.of K))]
    [Subsingleton (sheafCohomology X S.X₁ n₀)] [Subsingleton (sheafCohomology X S.X₁ n₁)] :
    sheafCohomology X S.X₂ n₀ ≃ₗ[K] sheafCohomology X S.X₃ n₀ :=
  LinearEquiv.ofBijective (sheafCohomology.mapOver K S.g n₀)
    ⟨sheafCohomology.map_g_injective_of_subsingleton hS n₀,
      sheafCohomology.map_g_surjective_of_subsingleton hS n₀ n₁ h⟩

include hS h in
/-- Dimension form: `H^{n₀}(M'') = H^{n₁}(M'') = 0` ⇒ `h^{n₁}(M') = h^{n₁}(M)`. -/
theorem sheafCohomology.finrank_eq_of_subsingleton_right (K : Type u) [CommRing K]
    [X.Over (Spec (CommRingCat.of K))]
    [Subsingleton (sheafCohomology X S.X₃ n₀)] [Subsingleton (sheafCohomology X S.X₃ n₁)] :
    Module.finrank K (sheafCohomology X S.X₁ n₁) = Module.finrank K (sheafCohomology X S.X₂ n₁) :=
  (sheafCohomology.equivOfSubsingletonRight hS n₀ n₁ h K).finrank_eq

include hS in
/-- Dimensions do not increase: `H^{n}(M'') = 0` ⇒ `h^n(M) ≤ h^n(M')` (in finite dimension). -/
theorem sheafCohomology.finrank_le_of_subsingleton (K : Type u) [Field K]
    [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
    [Subsingleton (sheafCohomology X S.X₃ n)] [FiniteDimensional K (sheafCohomology X S.X₁ n)] :
    Module.finrank K (sheafCohomology X S.X₂ n) ≤ Module.finrank K (sheafCohomology X S.X₁ n) :=
  LinearMap.finrank_le_finrank_of_surjective (f := sheafCohomology.mapOver K S.f n)
    (sheafCohomology.map_f_surjective_of_subsingleton hS n)

end LongExact

end AlgebraicGeometry

end
