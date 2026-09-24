import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristicDef
import MiyaokaMori.CategoryTheory.ExtPostcompLinear

/-! # Linear maps on sheaf cohomology

A morphism of modules `f : M ⟶ N` induces a `Γ(X, O_X)`-linear map `H^n(X, M) → H^n(X, N)` (also
`K`-linear when `X` is a `K`-scheme), functorially in `f` (identity, composition). Isomorphic
modules have linearly isomorphic `H^n`, hence equal `h^n` over `K` and equal Euler characteristic.

Proof sketch:
1. `H^n(X, M) = Ext^n(ℤ_X, M)`; `f` acts by postcomposition with `Ext.mk₀ f` (Mathlib's
   `Sheaf.H.map`), and a scalar `r` acts by postcomposition with `Ext.mk₀ μ_r` (`moduleSheafH`).
2. `f` is `O_X`-linear, so `μ_r^M ≫ f = f ≫ μ_r^N` (on each open set this is `map_smul` of `f(U)`);
   associativity of `Ext` composition gives `f_*(r • x) = r • f_*(x)`.
3. The `K`-structure is restriction of scalars along `K → Γ(X, O_X)` (`Module.compHom`), so a
   `Γ(X, O_X)`-linear map is automatically `K`-linear.
4. The linear map is produced by an existence theorem plus `Classical.choose` (for compile
   performance only, see the implementation note below); `sheafCohomology.map_apply` shows that it
   is `Sheaf.H.map`.
5. Functoriality comes from `Sheaf.H.map_id_apply` / `map_comp_apply`; an isomorphism `e` gives
   mutually inverse linear maps, hence a `LinearEquiv`, equal `finrank`, and equal `χ` termwise.

Source: functoriality of cohomology (Stacks 01E0).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The underlying morphism of abelian sheaves of a morphism of modules. -/
abbrev Scheme.Modules.toAddCommGrpSheafMap {M N : X.Modules} (f : M ⟶ N) :
    M.toAddCommGrpSheaf ⟶ N.toAddCommGrpSheaf :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map f

/-- `f` is `O_X`-linear: `μ_r^M ≫ f = f ≫ μ_r^N`. -/
theorem Scheme.Modules.smulEnd_naturality {M N : X.Modules} (f : M ⟶ N) (r : Γ(X, ⊤)) :
    M.smulEnd r ≫ Scheme.Modules.toAddCommGrpSheafMap f =
      Scheme.Modules.toAddCommGrpSheafMap f ≫ N.smulEnd r := by
  apply Sheaf.hom_ext
  ext U x
  exact ((f.val.app U).hom.map_smul _ x)

theorem Scheme.Modules.toAddCommGrpSheafMap_id (M : X.Modules) :
    Scheme.Modules.toAddCommGrpSheafMap (𝟙 M) = 𝟙 M.toAddCommGrpSheaf :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map_id M

theorem Scheme.Modules.toAddCommGrpSheafMap_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    Scheme.Modules.toAddCommGrpSheafMap (f ≫ g) =
      Scheme.Modules.toAddCommGrpSheafMap f ≫ Scheme.Modules.toAddCommGrpSheafMap g :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map_comp f g

/-- Unfolding of the scalar action: `r • x` is `x` postcomposed with `μ_r` (definition of
`moduleSheafH`). -/
theorem Scheme.Modules.smul_sheafH {M : X.Modules} (n : ℕ) (r : Γ(X, ⊤))
    (x : Sheaf.H M.toAddCommGrpSheaf n) :
    r • x = x.comp (Abelian.Ext.mk₀ (M.smulEnd r)) (add_zero n) := rfl

/- Implementation note (compile performance): `sheafCohomology` is a `def` whose `HasSheafify` proof
   term is abstracted by Lean into an auxiliary theorem, while the `Ext` lemmas carry the proof term
   verbatim; the two differ only in proof-irrelevant arguments, but the kernel, meeting reducible
   instances (`toAddCommMonoid`, …), unfolds the group structure of `Ext` instead of comparing
   arguments first, and each comparison takes seconds. Therefore the linear maps are produced by an
   existence theorem plus `Classical.choose`: the crossing happens once, inside the proof of the
   existence theorem, and the body of the `def` only mentions the constant `sheafCohomology`. -/

theorem sheafCohomology.exists_map {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    ∃ φ : sheafCohomology X M n →ₗ[Γ(X, ⊤)] sheafCohomology X N n,
      ∀ x : sheafCohomology X M n,
        φ x = Sheaf.H.map (Scheme.Modules.toAddCommGrpSheafMap f) n x :=
  ⟨Abelian.Ext.postcompLinear M.smulEnd N.smulEnd (Scheme.Modules.smul_sheafH n)
    (Scheme.Modules.smul_sheafH n) (Scheme.Modules.toAddCommGrpSheafMap f)
    (Scheme.Modules.smulEnd_naturality f), fun _ => rfl⟩

/-- The `Γ(X, O_X)`-linear map `H^n(X, M) → H^n(X, N)` induced by `f`. -/
def sheafCohomology.map {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    sheafCohomology X M n →ₗ[Γ(X, ⊤)] sheafCohomology X N n :=
  Classical.choose (sheafCohomology.exists_map f n)

/-- Unfolding: `f_*` is Mathlib's `Sheaf.H.map` (postcomposition with `Ext.mk₀ f`). -/
theorem sheafCohomology.map_apply {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (x : sheafCohomology X M n) :
    sheafCohomology.map f n x = Sheaf.H.map (Scheme.Modules.toAddCommGrpSheafMap f) n x :=
  Classical.choose_spec (sheafCohomology.exists_map f n) x

@[simp]
theorem sheafCohomology.map_id (M : X.Modules) (n : ℕ) :
    sheafCohomology.map (𝟙 M) n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [sheafCohomology.map_apply, Scheme.Modules.toAddCommGrpSheafMap_id]
  exact Sheaf.H.map_id_apply _

theorem sheafCohomology.map_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    sheafCohomology.map (f ≫ g) n = (sheafCohomology.map g n).comp (sheafCohomology.map f n) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, sheafCohomology.map_apply, sheafCohomology.map_apply,
    sheafCohomology.map_apply, Scheme.Modules.toAddCommGrpSheafMap_comp]
  exact Sheaf.H.map_comp_apply _ _ _

/-- Isomorphic modules have `Γ(X, O_X)`-linearly isomorphic cohomology. -/
def sheafCohomology.mapIso {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    sheafCohomology X M n ≃ₗ[Γ(X, ⊤)] sheafCohomology X N n :=
  LinearEquiv.ofLinearMap (sheafCohomology.map e.hom n) (sheafCohomology.map e.inv n)
    (by rw [← sheafCohomology.map_comp, e.inv_hom_id, sheafCohomology.map_id])
    (by rw [← sheafCohomology.map_comp, e.hom_inv_id, sheafCohomology.map_id])

section OverField

variable (K : Type u) [CommRing K] [X.Over (Spec (CommRingCat.of K))]

/-- On a `K`-scheme, the `K`-linear map `H^n(X, M) → H^n(X, N)` induced by `f`. -/
def sheafCohomology.mapOver {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    sheafCohomology X M n →ₗ[K] sheafCohomology X N n where
  toFun := sheafCohomology.map f n
  map_add' := _root_.map_add _
  map_smul' _ x := (sheafCohomology.map f n).map_smul _ x

@[simp]
theorem sheafCohomology.mapOver_apply {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (x : sheafCohomology X M n) :
    sheafCohomology.mapOver K f n x = sheafCohomology.map f n x := rfl

@[simp]
theorem sheafCohomology.mapOver_id (M : X.Modules) (n : ℕ) :
    sheafCohomology.mapOver K (𝟙 M) n = LinearMap.id := by
  ext x; simp

theorem sheafCohomology.mapOver_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    sheafCohomology.mapOver K (f ≫ g) n =
      (sheafCohomology.mapOver K g n).comp (sheafCohomology.mapOver K f n) := by
  ext x; simp [sheafCohomology.map_comp]

/-- Isomorphic modules have `K`-linearly isomorphic cohomology. -/
def sheafCohomology.mapIsoOver {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    sheafCohomology X M n ≃ₗ[K] sheafCohomology X N n :=
  LinearEquiv.ofLinearMap (sheafCohomology.mapOver K e.hom n) (sheafCohomology.mapOver K e.inv n)
    (by rw [← sheafCohomology.mapOver_comp, e.inv_hom_id, sheafCohomology.mapOver_id])
    (by rw [← sheafCohomology.mapOver_comp, e.hom_inv_id, sheafCohomology.mapOver_id])

theorem sheafCohomology.finrank_eq_of_iso {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    Module.finrank K (sheafCohomology X M n) = Module.finrank K (sheafCohomology X N n) :=
  (sheafCohomology.mapIsoOver K e n).finrank_eq

theorem sheafCohomology.subsingleton_of_iso {M N : X.Modules} (e : M ≅ N) (n : ℕ)
    [Subsingleton (sheafCohomology X N n)] : Subsingleton (sheafCohomology X M n) :=
  (sheafCohomology.mapIso e n).toEquiv.subsingleton

end OverField

/-- The Euler characteristic depends only on the isomorphism class of the module. -/
theorem sheafEulerCharacteristic_eq_of_iso {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] {M N : X.Modules} (e : M ≅ N) :
    sheafEulerCharacteristic (k := k) X M = sheafEulerCharacteristic (k := k) X N := by
  unfold sheafEulerCharacteristic
  exact finsum_congr fun i => by rw [sheafCohomology.finrank_eq_of_iso k e i]

end AlgebraicGeometry

end
