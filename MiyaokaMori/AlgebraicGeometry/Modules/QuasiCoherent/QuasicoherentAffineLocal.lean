import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization

/-! # Affine-local principles for quasi-coherent sheaves

(1) On an affine open `U = Spec A`, `F ↦ Γ(U, F)` is an exact equivalence from `QCoh(U)` to
`A`-modules (Stacks 01IB); (2) for affine `U ⊆ Y` and affine `W ⊆ f⁻¹U`,
`Γ(W, f^*F) = Γ(W) ⊗_{Γ(U)} Γ(U, F)` (Stacks 01I9); (3) morphisms and isomorphisms between
quasi-coherent sheaves are determined by their values on a basis of affine opens, compatibly with
restriction.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

namespace QcAffineLocalAux

variable {X : Scheme.{u}}

/-- On an affine open `U`: if an ideal `I` of `Γ(U, O)` contains, for every point `p ∈ U`, a power of some
`h` with `p ∈ D(h)`, then `I = ⊤`. -/
theorem ideal_eq_top {U : X.Opens} (hU : IsAffineOpen U) (I : Ideal Γ(X, U))
    (h : ∀ p : X, p ∈ U → ∃ (f : Γ(X, U)) (n : ℕ), p ∈ X.basicOpen f ∧ f ^ n ∈ I) : I = ⊤ := by
  by_contra hI
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  let 𝔭 : Spec Γ(X, U) := ⟨m, hm.isPrime⟩
  have hp : hU.fromSpec 𝔭 ∈ U := by
    have : hU.fromSpec 𝔭 ∈ Set.range hU.fromSpec := ⟨𝔭, rfl⟩
    rw [hU.range_fromSpec] at this
    exact this
  obtain ⟨f, n, hpf, hfn⟩ := h _ hp
  have h1 : 𝔭 ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := hpf
  rw [hU.fromSpec_preimage_basicOpen] at h1
  exact h1 (hm.isPrime.mem_of_pow_mem n (hIm hfn))


/-- The core of "⇒": for quasi-coherent sheaves on an affine open `U`, `ker g_U ⊆ im f_U`. -/
theorem range_of_exact (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    (hS : S.Exact) {U : X.Opens} (hU : IsAffineOpen U) (x : Γ(S.X₂, U)) (hx : S.g.app U x = 0) :
    ∃ z : Γ(S.X₁, U), S.f.app U z = x := by
  let I : Ideal Γ(X, U) :=
    { carrier := {a | ∃ z : Γ(S.X₁, U), S.f.app U z = a • x}
      add_mem' := by
        rintro a b ⟨z, hz⟩ ⟨w, hw⟩
        exact ⟨z + w, by rw [map_add, hz, hw, add_smul]⟩
      zero_mem' := ⟨0, by rw [map_zero, zero_smul]⟩
      smul_mem' := by
        rintro c a ⟨z, hz⟩
        exact ⟨c • z, by rw [Scheme.Modules.Hom.app_smul, hz, smul_eq_mul, mul_smul]⟩ }
  have hI : I = ⊤ := by
    refine ideal_eq_top hU I fun p hp => ?_
    obtain ⟨V, hVU, hpV, y, hy⟩ :=
      (Scheme.Modules.exact_iff_locally_lift_sections S).mp hS U x hx p hp
    obtain ⟨h, hhV, hph⟩ := hU.exists_basicOpen_le ⟨p, hpV⟩ hp
    let y' := S.X₁.presheaf.map (homOfLE hhV).op y
    obtain ⟨n, t, ht⟩ := S.X₁.exists_pow_smul_eq_map_basicOpen hU h y'
    have hnat : ∀ {A B : X.Opens} (i : A ⟶ B) (w : Γ(S.X₁, B)),
        S.f.app A (S.X₁.presheaf.map i.op w) = S.X₂.presheaf.map i.op (S.f.app B w) :=
      fun i w => congr($(S.f.mapPresheaf.naturality i.op) w)
    have hy' : S.f.app (X.basicOpen h) y' =
        S.X₂.presheaf.map (homOfLE (X.basicOpen_le h)).op x := by
      rw [hnat, hy, ← S.X₂.presheaf.map_comp_apply]
      rfl
    have hzero : S.X₂.presheaf.map (homOfLE (X.basicOpen_le h)).op (S.f.app U t - h ^ n • x) = 0 := by
      rw [map_sub, ← hnat, ht, Scheme.Modules.Hom.app_smul, hy', Scheme.Modules.map_smul, map_pow,
        sub_self]
    obtain ⟨k, hk⟩ := S.X₂.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero hU h _ hzero
    refine ⟨h, k + n, hph, h ^ k • t, ?_⟩
    rw [smul_sub, sub_eq_zero] at hk
    rw [Scheme.Modules.Hom.app_smul, hk, pow_add, mul_smul]
  obtain ⟨z, hz⟩ : (1 : Γ(X, U)) ∈ I := by rw [hI]; trivial
  exact ⟨z, by rw [hz, one_smul]⟩

end QcAffineLocalAux

theorem AlgebraicGeometry.Scheme.Modules.gammaAffine_exact_iff {X : AlgebraicGeometry.Scheme.{u}}
    (S : CategoryTheory.ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] :
    S.Exact ↔ ∀ U : X.affineOpens,
      Function.Exact (S.f.app U.1).hom (S.g.app U.1).hom := by
  have hzero : ∀ (V : X.Opens) (z : Γ(S.X₁, V)), S.g.app V (S.f.app V z) = 0 := fun V z => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, S.zero]
    rfl
  constructor
  · intro hS U x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := QcAffineLocalAux.range_of_exact S hS U.2 x hx
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      exact hzero U.1 z
  · intro h
    rw [Scheme.Modules.exact_iff_locally_lift_sections]
    intro U x hx p hp
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hp U.isOpen
    have hVU' : V ≤ U := hVU
    have hx' : S.g.app V (S.X₂.presheaf.map (homOfLE hVU').op x) = 0 := by
      have := congr($(S.g.mapPresheaf.naturality (homOfLE hVU').op) x)
      refine Eq.trans this ?_
      change S.X₃.presheaf.map (homOfLE hVU').op (S.g.app U x) = 0
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := ((h ⟨V, hV⟩) _).mp hx'
    exact ⟨V, hVU', hpV, y, hy⟩

theorem AlgebraicGeometry.Scheme.Modules.isIso_of_affine {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : ∀ U : X.affineOpens, Function.Bijective (φ.app U.1).hom) : CategoryTheory.IsIso φ := by
  have hb : Opens.IsBasis (Set.range (fun U : X.affineOpens => (U.1 : X.Opens))) := by
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  have h1 : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    TopCat.Sheaf.isIso_iff_isIso_basis hb (fun U =>
      (ConcreteCategory.isIso_iff_bijective _).mpr (h U))
  exact isIso_of_reflects_iso (C := SheafOfModules.{u} X.ringCatSheaf) φ
    (SheafOfModules.toSheaf X.ringCatSheaf)

-- Sections of the pullback are in `QcPullbackAffineSections`.

end
