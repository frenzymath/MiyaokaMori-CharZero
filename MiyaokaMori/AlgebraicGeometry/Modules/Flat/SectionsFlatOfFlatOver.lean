import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.Stacks01u4
import Mathlib.RingTheory.Flat.Basic

/-! # Sections of a flat quasi-coherent sheaf over an affine base are flat

If `f : X ⟶ Spec A`, `M` is quasi-coherent and flat over `Spec A`, and `V ⊆ X` is an affine
open, then `Γ(M, V)` is a flat `A`-module. This follows from the affine characterization of
flatness (`isFlatOver_iff_affine`, Stacks 01U4) applied to `U := V` and the affine open `⊤` of
the base, transported along the bijective ring map `A → Γ(Spec A, ⊤)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- **Flatness along a bijective ring map.** If `N` is a flat `S`-module and `g : R →+* S` is
bijective, then `N` with the module structure `Module.compHom N g` is a flat `R`-module.

Proof: make `S` an `R`-algebra via `g`; then `R`, `S`, `N` form a scalar tower, `S` is flat
over `R` (`RingHom.Flat.of_bijective`), and a flat module over a flat algebra is flat
(`Module.Flat.trans`, Stacks 00HC / Bourbaki AC I §2.7 Cor. 3). -/
theorem flat_compHom_of_bijective {R S N : Type u} [CommRing R] [CommRing S] [AddCommGroup N]
    [Module S N] [Module.Flat S N] (g : R →+* S) (hg : Function.Bijective g) :
    letI : Module R N := Module.compHom N g
    Module.Flat R N := by
  letI : Algebra R S := g.toAlgebra
  letI : Module R N := Module.compHom N g
  haveI : IsScalarTower R S N := ⟨fun r s n => by
    change (g r * s) • n = g r • s • n
    rw [mul_smul]⟩
  haveI : Module.Flat R S := RingHom.Flat.of_bijective hg
  exact Module.Flat.trans R S N

/-- **Application of Stacks 01U4.** If `M` is flat over `Spec A` and `V ⊆ X` is an affine open,
then `Γ(M, V)` is a flat `A`-module, where `A` acts through
`A ≅ Γ(Spec A, ⊤) → Γ(X, ⊤) → Γ(X, V)`.

Proof: `isFlatOver_iff_affine` with `U := V` and the affine open `⊤` of the base shows that
`Γ(M, V)` is flat over `Γ(Spec A, ⊤)` via `f.appLE ⊤ V _`; `flat_compHom_of_bijective` transports
this along the bijective ring map `(ΓSpecIso A).inv.hom : A →+* Γ(Spec A, ⊤)`. The resulting
`A`-module structure agrees definitionally with the one in the statement (unfold
`Scheme.Hom.appLE` and `f ⁻¹ᵁ ⊤ = ⊤`).

Edge cases: if `M = 0` then `Γ(M, V) = 0` is flat; if `A = 0` then `Spec A = ∅`, `X = ∅`, and all
modules are zero. -/
theorem sectionsOverTop_flat_of_isFlatOver {A : CommRingCat.{u}} {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec A) (M : X.Modules) [M.IsQuasicoherent]
    (hM : AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver f M) (V : X.Opens)
    (hV : AlgebraicGeometry.IsAffineOpen V) :
    Module.Flat A ((ModuleCat.restrictScalars
      ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop).hom).obj (M.sectionsOverTop V)) := by
  letI : Module Γ(Spec A, ⊤) Γ(M, V) :=
    Module.compHom _ (f.appLE (⊤ : (Spec A).Opens) V le_top).hom
  have h1 : Module.Flat Γ(Spec A, ⊤) Γ(M, V) :=
    (AlgebraicGeometry.Scheme.Modules.isFlatOver_iff_affine f M).mp hM ⟨V, hV⟩
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ le_top
  have h2 := flat_compHom_of_bijective (N := Γ(M, V)) (S := Γ(Spec A, ⊤)) (R := A)
    (AlgebraicGeometry.Scheme.ΓSpecIso A).inv.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.bijective)
  exact h2

end AlgebraicGeometry.Scheme.Modules

end
