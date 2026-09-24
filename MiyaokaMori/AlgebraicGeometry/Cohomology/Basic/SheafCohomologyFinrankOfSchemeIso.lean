import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PushforwardInvIsoPullback
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.SheafCohomologyClosedImmersionLinear
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap

/-! # Invariance of cohomology dimensions under scheme isomorphisms

The dimension of sheaf cohomology is invariant under an isomorphism of schemes, allowing the base
ring to change along a ring isomorphism `σ : K ≃+* K'`: if `e : Z ≅ X` is an isomorphism of
schemes, `Z` a `K`-scheme, `X` a `K'`-scheme, with structure morphisms compatible via `e` and
`Spec σ`, then for every module `N` on `X` and every `n`, `dim_K H^n(Z, e^*N) = dim_{K'} H^n(X, N)`.
(`K, K'` only need to be commutative rings: `LinearEquiv.finrank_eq` and `rank_eq_of_equiv_equiv`
do not require fields; this also avoids a diamond between `Field.toSemiring` and the `CommRingCat`
carrier instances.)

Proof sketch:
1. The isomorphism `e.inv : X ⟶ Z` is a closed immersion, and the `K'`-linear form of Stacks 02UV
   (`sheafCohomologyClosedImmersionLinearEquiv`, with `Z` carrying the transported `K'`-structure
   `e.hom ≫ (X ↘ Spec K')`) gives `dim_{K'} H^n(X, N) = dim_{K'} H^n(Z, (e.inv)_* N)`.
2. On the abelian group `H^n(Z, M)` the transported `K'`-structure and the original `K`-structure
   correspond via `σ`: `c •_K x = (σ c) •_{K'} x`, since both scalar actions factor through
   multiplication by global functions `Γ(Z, ⊤)`, and compatibility of the structure morphisms plus
   naturality of `ΓSpecIso` show that the two ring maps `K → Γ(Z, ⊤)`, `K' → Γ(Z, ⊤)` agree via `σ`.
   Hence `Module.rank` agrees (`rank_eq_of_equiv_equiv`), and so does `finrank`.
3. `(e.inv)_* N ≅ e.hom^* N` (`Scheme.Modules.pushforwardInvIsoPullback`), and cohomology
   dimensions are invariant under isomorphisms of modules (`sheafCohomology.finrank_eq_of_iso`).

Source: Stacks 02UV. Used in the paper for the base change of fibre cohomology (the canonical
isomorphism of residue fields `κ(t) ≅ κ(p)` preserves dimensions).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- the `letI` in the proofs must stay inline (the instance term on the right of the statement must be
-- literally the same); it cannot be replaced by `let`
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Comparison of two base structures on the same scheme `Z`: if the `K`-structure of `Z` is
`s ≫ Spec σ` (`s : Z ⟶ Spec K'`, `σ : K ≃+* K'`), then the `K`-dimension of `H^n(Z, M)` equals its
`K'`-dimension (with `s` as structure morphism).

Proof: both scalar actions factor through `Γ(Z, ⊤)` (`sheafCohomology.moduleOver` is
`Module.compHom`), and `(ΓSpecIso K).inv ≫ (s ≫ Spec σ).appTop = σ ≫ (ΓSpecIso K').inv ≫ s.appTop`
(`ΓSpecIso_inv_naturality`), so `c • x = σ c • x`; `rank_eq_of_equiv_equiv` (with
`j = AddEquiv.refl`) gives equality of ranks. -/
theorem sheafCohomology_finrank_eq_of_ringEquiv_over {K K' : Type u} [CommRing K] [CommRing K']
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] (s : Z ⟶ Spec (CommRingCat.of K'))
    (σ : K ≃+* K')
    (hs : s ≫ Spec.map (CommRingCat.ofHom (σ : K →+* K')) = Z ↘ Spec (CommRingCat.of K))
    (M : Z.Modules) (n : ℕ) :
    Module.finrank K (sheafCohomology Z M n)
      = (letI : Z.Over (Spec (CommRingCat.of K')) := ⟨s⟩
         Module.finrank K' (sheafCohomology Z M n)) := by
  letI : Z.Over (Spec (CommRingCat.of K')) := ⟨s⟩
  have key : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Z ↘ Spec (CommRingCat.of K)).appTop
      = CommRingCat.ofHom (σ : K →+* K') ≫
        ((Scheme.ΓSpecIso (CommRingCat.of K')).inv ≫ s.appTop) := by
    rw [← hs, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  have hsmul : ∀ (c : K) (x : sheafCohomology Z M n),
      (c • x : sheafCohomology Z M n) = (σ c • x : sheafCohomology Z M n) := by
    intro c x
    show ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Z ↘ Spec (CommRingCat.of K)).appTop).hom c • x
      = ((Scheme.ΓSpecIso (CommRingCat.of K')).inv ≫ s.appTop).hom (σ c) • x
    rw [key]
    rfl
  show Cardinal.toNat _ = Cardinal.toNat _
  congr 1
  exact rank_eq_of_equiv_equiv (σ : K → K') (AddEquiv.refl _) σ.bijective
    (fun c x => by simpa using hsmul c x)

/-- **Cohomology dimensions are invariant under scheme isomorphisms** (base changed along `σ`).
See the module docstring. -/
theorem sheafCohomology_finrank_eq_of_schemeIso {K K' : Type u} [CommRing K] [CommRing K']
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K'))]
    (e : Z ≅ X) (σ : K ≃+* K')
    (hσ : e.hom ≫ (X ↘ Spec (CommRingCat.of K')) ≫ Spec.map (CommRingCat.ofHom (σ : K →+* K'))
      = Z ↘ Spec (CommRingCat.of K))
    (N : X.Modules) (n : ℕ) :
    Module.finrank K (sheafCohomology Z ((Scheme.Modules.pullback e.hom).obj N) n)
      = Module.finrank K' (sheafCohomology X N n) := by
  rw [← sheafCohomology.finrank_eq_of_iso K
    ((Scheme.Modules.pushforwardInvIsoPullback e).app N) n]
  rw [sheafCohomology_finrank_eq_of_ringEquiv_over (e.hom ≫ (X ↘ Spec (CommRingCat.of K'))) σ
    (by rw [Category.assoc]; exact hσ) _ n]
  letI : Z.Over (Spec (CommRingCat.of K')) := ⟨e.hom ≫ (X ↘ Spec (CommRingCat.of K'))⟩
  haveI : e.inv.IsOver (Spec (CommRingCat.of K')) :=
    ⟨by show e.inv ≫ e.hom ≫ (X ↘ Spec (CommRingCat.of K')) = X ↘ Spec (CommRingCat.of K')
        rw [Iso.inv_hom_id_assoc]⟩
  exact (sheafCohomologyClosedImmersionLinearEquiv (K := K') e.inv N n).finrank_eq.symm

/-- **The same result with explicit structure morphisms**: `sZ : Z ⟶ Spec K`, `sX : X ⟶ Spec K'` are
explicit data (packaged as `Over` instances by `letI` in the statement), the base isomorphism is an
isomorphism `σ : .of K ≅ .of K'` in `CommRingCat`, and the compatibility is
`e.hom ≫ sX ≫ Spec.map σ.hom = sZ`. This is the shape needed for the affine base change of fibre
cohomology; it avoids expensive instance synthesis and defeq checks at the use site. -/
theorem sheafCohomology_finrank_eq_of_schemeIso' {K K' : Type u} [CommRing K] [CommRing K']
    {Z X : Scheme.{u}} (sZ : Z ⟶ Spec (CommRingCat.of K)) (sX : X ⟶ Spec (CommRingCat.of K'))
    (e : Z ≅ X) (σ : CommRingCat.of K ≅ CommRingCat.of K')
    (hσ : e.hom ≫ sX ≫ Spec.map σ.hom = sZ) (N : X.Modules) (n : ℕ) :
    (letI : Z.Over (Spec (CommRingCat.of K)) := ⟨sZ⟩
     Module.finrank K (sheafCohomology Z ((Scheme.Modules.pullback e.hom).obj N) n))
      = (letI : X.Over (Spec (CommRingCat.of K')) := ⟨sX⟩
         Module.finrank K' (sheafCohomology X N n)) := by
  letI : Z.Over (Spec (CommRingCat.of K)) := ⟨sZ⟩
  letI : X.Over (Spec (CommRingCat.of K')) := ⟨sX⟩
  have hσ' : e.hom ≫ sX ≫
      Spec.map (CommRingCat.ofHom (σ.commRingCatIsoToRingEquiv : K →+* K')) = sZ := by
    have hσhom : CommRingCat.ofHom (σ.commRingCatIsoToRingEquiv : K →+* K') = σ.hom :=
      CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
    rw [hσhom]
    exact hσ
  exact sheafCohomology_finrank_eq_of_schemeIso e σ.commRingCatIsoToRingEquiv hσ' N n

end AlgebraicGeometry

end
