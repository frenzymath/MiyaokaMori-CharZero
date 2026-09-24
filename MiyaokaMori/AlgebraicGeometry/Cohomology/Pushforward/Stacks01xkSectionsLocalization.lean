import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcLocalizedModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternatingDefs
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Sections of a quasi-coherent module over a basic open are a localization

**Statement.** `M` a quasi-coherent module on a scheme `X`, `a : A →+* Γ(X, O_X)`, `g ∈ A`, `V ⊆ X`
an affine open and `W = X.basicOpen (a g |_V) = V ∩ D(a g)`. Then the restriction
`Γ(M, V) → Γ(M, W)`, viewed as an `A`-linear map (scalars via `a` and restriction), is the
localization of the `A`-module `Γ(M, V)` at the powers of `g`.

**Proof** (Stacks 01I8 / 01P7, Hartshorne II.5.1(c)). The general statement is
`Scheme.Modules.isLocalizedModule_basicOpen` (`QcLocalizedModule.lean`): for `h ∈ Γ(X, V)`,
the restriction `Γ(M, V) → Γ(M, D(h))` is the localization of the `Γ(X, V)`-module `Γ(M, V)` at the
powers of `h`. Here `h = a g |_V`, `W = D(h)`, and the scalars are restricted along
`φ = (res_V ∘ a) : A → Γ(X, V)`, which maps `powers g` onto `powers h`; the three axioms of
`IsLocalizedModule (powers g)` for the `A`-linear map are read off from those for `powers h`:
units — `g^n` acts on `Γ(M, W)` as `φ(g)^n = h^n`, which acts bijectively; surjectivity up to
powers — an `h^n` works, hence `g^n`; kernel — `h^n • x₁ = h^n • x₂` reads `g^n • x₁ = g^n • x₂`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) {A : Type u} [CommRing A]
  (a : A →+* Γ(X, ⊤))

/-- restriction of a ring section twice is restriction once -/
theorem ring_res_top_res {U V : X.Opens} (h : V ≤ U) (z : Γ(X, ⊤)) :
    X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op z) =
      X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op z := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

theorem sectionsOverTopRestrict_apply {V W : X.Opens} (hle : W ≤ V) (s : Γ(M, V)) :
    ((ModuleCat.restrictScalars a).map (M.sectionsOverTopRestrict hle)).hom s =
      M.presheaf.map (homOfLE hle).op s := rfl

/-- For a quasi-coherent module on an affine open `V`: restriction to the basic open
`D(a g) ∩ V = X.basicOpen (a g |_V)` is the localization of the `A`-module at the powers of `g`. -/
theorem isLocalizedModule_sectionsOverTopRestrict_basicOpen [M.IsQuasicoherent] (g : A)
    {V W : X.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    (hW : W = X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (a g))) (hle : W ≤ V) :
    IsLocalizedModule (Submonoid.powers g)
      ((ModuleCat.restrictScalars a).map (M.sectionsOverTopRestrict hle)).hom := by
  subst hW
  set h : Γ(X, V) := X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (a g) with hh
  -- the `Γ(X, V)`-module structure of `Γ(M, D(h))` through restriction, and the restriction map
  let _ : Module Γ(X, V) Γ(M, X.basicOpen h) :=
    Module.compHom Γ(M, X.basicOpen h) (X.presheaf.map (homOfLE hle).op).hom
  let g' : Γ(M, V) →ₗ[Γ(X, V)] Γ(M, X.basicOpen h) :=
    { toFun := M.presheaf.map (homOfLE hle).op
      map_add' := fun a b => by simp
      map_smul' := fun r m => by rw [Scheme.Modules.map_smul]; rfl }
  have L : IsLocalizedModule (Submonoid.powers h) g' :=
    isLocalizedModule_basicOpen M hV h (fun _ _ => rfl) g' (fun _ => rfl)
  -- `g^n` acts on `Γ(M, W)` as `h^n` does
  have hresn : ∀ n : ℕ, X.presheaf.map (homOfLE (le_top : X.basicOpen h ≤ ⊤)).op (a (g ^ n)) =
      X.presheaf.map (homOfLE hle).op (h ^ n) := by
    intro n
    rw [map_pow, map_pow, map_pow]
    exact congrArg (· ^ n) (ring_res_top_res hle (a g)).symm
  constructor
  · rintro ⟨x, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hbij := (Module.End.isUnit_iff _).mp (L.map_units ⟨h ^ n, n, rfl⟩)
    have hfun : ⇑(algebraMap A (Module.End A
        ((ModuleCat.restrictScalars a).obj (M.sectionsOverTop (X.basicOpen h)))) (g ^ n)) =
        ⇑(algebraMap Γ(X, V) (Module.End Γ(X, V) Γ(M, X.basicOpen h)) (h ^ n)) := by
      funext s
      show X.presheaf.map (homOfLE (le_top : X.basicOpen h ≤ ⊤)).op (a (g ^ n)) •
        (id s : Γ(M, X.basicOpen h)) = _
      rw [hresn]
      rfl
    rw [hfun]
    exact hbij
  · intro y
    let y' : Γ(M, X.basicOpen h) := y
    obtain ⟨⟨t, s⟩, hts⟩ := L.surj y'
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    refine ⟨(t, ⟨g ^ n, n, rfl⟩), ?_⟩
    show (⟨g ^ n, n, rfl⟩ : Submonoid.powers g) • y = M.presheaf.map (homOfLE hle).op t
    rw [Submonoid.smul_def]
    show X.presheaf.map (homOfLE (le_top : X.basicOpen h ≤ ⊤)).op (a (g ^ n)) •
      (id y : Γ(M, X.basicOpen h)) = _
    rw [hresn]
    rw [Submonoid.smul_def, ← hn] at hts
    exact hts
  · intro x₁ x₂ hx
    let y₁ : Γ(M, V) := x₁
    let y₂ : Γ(M, V) := x₂
    have hx' : g' y₁ = g' y₂ := hx
    obtain ⟨c, hc⟩ := L.exists_of_eq hx'
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def]
    show X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (a (g ^ n)) • y₁ =
      X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (a (g ^ n)) • y₂
    rw [map_pow, map_pow, ← hh]
    simp only [Submonoid.smul_def, ← hn] at hc
    exact hc

end AlgebraicGeometry.Scheme.Modules

end
