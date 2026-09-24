import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternatingElementwise
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift

/-! # Čech acyclicity of a quotient

Let `0 → F → G → H → 0` be a short exact sequence of `O_X`-modules and `U : Fin n → X.Opens` a
finite family of opens. If `G(U_σ) → H(U_σ)` is surjective for every strictly increasing index tuple
`σ` (`U_σ = ⋂_k U_{σ_k}`), and the alternating Čech complexes of `F` and `G` have zero homology in
all positive degrees, then so does that of `H`.

Proof sketch (diagram chase on families of sections): let `s ∈ C^{q+1}(H)` be a cocycle.
Lift it termwise to `i ∈ C^{q+1}(G)` with `g(i) = s`. Then `g(d i) = d s = 0`, so by left exactness
of sections (`sections_of_exact_mono`) `d i = f(m)` with `m ∈ C^{q+2}(F)`; `f` is termwise injective
and `f(d m) = d d i = 0`, so `d m = 0`. Acyclicity of `F` in degree `q+2 > 0` gives `m = d m'`; put
`i₁ = i − f(m')`, so `d i₁ = 0`. Acyclicity of `G` in degree `q+1 > 0` gives `i₁ = d i'`; with
`t = g(i')`, `d t = g(i₁) = g(i) − g f(m') = s`.

Source: a step in the proof of Stacks 01EW (long exact sequence of a short exact sequence of Čech
complexes, done here directly as a diagram chase).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens)

theorem cechComplexAlt_homology_subsingleton_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (hsurj : ∀ (q : ℕ) (σ : Fin (q + 1) ↪o Fin n), Function.Surjective (S.g.app (⨅ k, U (σ k))))
    (h1 : ∀ p : ℕ, 0 < p → Subsingleton (((cechComplexAlt U S.X₁).homology (p : ℤ)) : Type u))
    (h2 : ∀ p : ℕ, 0 < p → Subsingleton (((cechComplexAlt U S.X₂).homology (p : ℤ)) : Type u))
    (p : ℕ) (hp : 0 < p) :
    Subsingleton (((cechComplexAlt U S.X₃).homology (p : ℤ)) : Type u) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hmono : Mono S.f := hS.mono_f
  have hfg : ∀ (W : X.Opens) (z : Γ(S.X₁, W)), S.g.app W (S.f.app W z) = 0 := fun W z =>
    congrArg (fun φ : S.X₁ ⟶ S.X₃ => (AlgebraicGeometry.Scheme.Modules.Hom.app φ W) z) S.zero
  apply cechComplexAlt_homology_subsingleton_of_family
  intro s hs
  choose i hi using fun σ : Fin (q + 2) ↪o Fin n => hsurj (q + 1) σ (s σ)
  have hgd : ∀ τ, S.g.app _ (cechFamilyD U S.X₂ (q + 1) i τ) = 0 := by
    intro τ
    have h := congrFun (cechFamilyD_map U S.g (q + 1) i) τ
    rw [show (fun σ => S.g.app _ (i σ)) = s from funext hi, hs] at h
    exact h
  choose m hm using fun τ =>
    (ModulesLocLiftAux.sections_of_exact_mono S hS.exact _).2 _ (hgd τ)
  have hmcoc : cechFamilyD U S.X₁ (q + 1 + 1) m = 0 := by
    funext τ
    apply (ModulesLocLiftAux.sections_of_exact_mono S hS.exact _).1
    have h := congrFun (cechFamilyD_map U S.f (q + 1 + 1) m) τ
    rw [show (fun σ => S.f.app _ (m σ)) = cechFamilyD U S.X₂ (q + 1) i from funext hm,
      cechFamilyD_comp] at h
    exact h.trans (map_zero _).symm
  obtain ⟨m', hm'⟩ := exists_family_of_homology_subsingleton U S.X₁ (q + 1)
    (h1 (q + 1 + 1) (by omega)) m hmcoc
  have hd1 : cechFamilyD U S.X₂ (q + 1) (i - fun σ => S.f.app _ (m' σ)) = 0 := by
    rw [cechFamilyD_sub, ← cechFamilyD_map, hm', sub_eq_zero]
    exact (funext hm).symm
  obtain ⟨i', hi'⟩ := exists_family_of_homology_subsingleton U S.X₂ q
    (h2 (q + 1) (by omega)) _ hd1
  refine ⟨fun σ => S.g.app _ (i' σ), ?_⟩
  rw [← cechFamilyD_map, hi']
  funext σ
  show S.g.app _ (i σ - S.f.app _ (m' σ)) = s σ
  rw [map_sub, hfg, sub_zero, hi]

end AlgebraicGeometry.Scheme.Modules

end
