import MiyaokaMori.Prelude
import Mathlib.RingTheory.Localization.Free
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfFreeAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01pbAffineOpen
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcLocalizedModule

/-! # A coherent sheaf with free stalks is locally free

On a locally Noetherian scheme, a coherent sheaf all of whose stalks are free modules is locally free.

Instead of the sheaf-theoretic route (lift a basis of `M_x` to sections, then spread out the kernel
and cokernel with Stacks 01B9 / 01Y1 / stalk exactness), the proof uses the affine-algebraic route,
Stacks 00NX ("a finitely presented module that is free at a prime is free on a principal
neighbourhood") in Mathlib's form `Module.FinitePresentation.exists_free_localizedModule_powers`:

1. Pick an affine open `U ∋ x`, `A := Γ(X, U)` (noetherian, `IsLocallyNoetherian.component_noetherian`),
   `N := Γ(M, U)` (finite over `A` by Stacks 01PB on an affine open,
   `finite_sections_of_isFiniteType`, hence finitely presented, `Module.finitePresentation_of_finite`).
2. `M_x` is the localization of `N` at the prime `p ⊂ A` of `x`, along the germ map
   (`isLocalizedModule_germ` below; `O_{X,x}` is `A_p` by `IsAffineOpen.isLocalization_stalk`).
   Proof: every element of the stalk is a germ of a section on a basic open `D(g) ∋ x`, `g ∉ p`,
   and on `D(g)` the restriction `N → Γ(M, D(g))` is the localization at `g`
   (quasi-coherence, `isLocalizedModule_basicOpen`); two sections with the same germ agree on some
   `D(g)`.
3. Since `M_x` is free over `O_{X,x} = A_p`, Mathlib gives `r ∉ p` with `N_r` free over `A_r`.
4. `V := D(r)` is an affine open containing `x`; `Γ(X, V) = A_r`
   (`IsAffineOpen.isLocalization_basicOpen`) and `Γ(M, V) = N_r` (`isLocalizedModule_basicOpen`),
   so `Γ(M, V)` is free over `Γ(X, V)` (transport of freeness along the semilinear equivalence
   `LocalizedModule.Away r N ≃ Γ(M, V)` over `A_r ≃ Γ(X, V)`), and finite by 01PB again.
5. `isLocallyFree_of_free_affine_sections` concludes.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CoherentFreeStalksAux

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Germs commute with the scalar action (Mathlib `PresheafOfModules.germ_smul`, spelled for
`X.Modules`). -/
theorem germ_smul' (M : X.Modules) {V : X.Opens} {y : X} (hy : y ∈ V) (r : Γ(X, V)) (m : Γ(M, V)) :
    M.presheaf.germ V y hy (r • m) = X.presheaf.germ V y hy r • M.presheaf.germ V y hy m :=
  PresheafOfModules.germ_smul (R := X.presheaf) M.val y V hy r m

/-- The restriction map `Γ(M, U) → Γ(M, X.basicOpen f)` as a `Γ(X, U)`-linear map, where
`Γ(M, X.basicOpen f)` carries the `Γ(X, U)`-module structure `Module.compHom` through restriction. -/
def resBasicOpen (M : X.Modules) {U : X.Opens} (f : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) :=
  letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  { toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
    map_add' := fun a b => by simp
    map_smul' := fun r m => by
      rw [Scheme.Modules.map_smul]; rfl }

/-- **The stalk of a quasi-coherent module at a point of an affine open is the localization of the
sections at the corresponding prime** (Stacks 01I8 in `IsLocalizedModule` form). The
`Γ(X, U)`-module structure on the stalk and the linear germ map are passed as parameters
(interface convention of `QcLocalizedModule`). -/
theorem isLocalizedModule_germ (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    [Module Γ(X, U) (M.presheaf.stalk x)]
    (hsmul : ∀ (r : Γ(X, U)) (m : M.presheaf.stalk x),
      r • m = X.presheaf.germ U x hx r • m)
    (g : Γ(M, U) →ₗ[Γ(X, U)] M.presheaf.stalk x)
    (hg : ∀ m, g m = M.presheaf.germ U x hx m) :
    IsLocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl g := by
  set p := hU.primeIdealOf ⟨x, hx⟩ with hp
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  -- `x ∈ D(f)` iff `f ∉ p`
  have hmem : ∀ f : Γ(X, U), x ∈ X.basicOpen f ↔ f ∈ p.asIdeal.primeCompl := fun f =>
    (X.mem_basicOpen f x hx).trans
      (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) p.asIdeal f)
  have hpow : ∀ (f : Γ(X, U)) (s : Submonoid.powers f), x ∈ X.basicOpen f →
      (s : Γ(X, U)) ∈ p.asIdeal.primeCompl := by
    intro f s hxf
    obtain ⟨k, hk⟩ := s.2
    rw [← hk]
    exact Submonoid.pow_mem _ ((hmem f).mp hxf) k
  refine ⟨fun s => ?_, fun m => ?_, fun {n n'} h => ?_⟩
  · -- `s` acts invertibly on the stalk
    have hs : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) s) := IsLocalization.map_units _ s
    rw [Module.End.isUnit_iff]
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun m => (↑hs.unit⁻¹ : X.presheaf.stalk x) • m, fun m => ?_, fun m => ?_⟩
    · simp only [Module.algebraMap_end_apply, hsmul]
      change (↑hs.unit⁻¹ : X.presheaf.stalk x) • ((hs.unit : X.presheaf.stalk x) • m) = m
      rw [smul_smul, Units.inv_mul, one_smul]
    · simp only [Module.algebraMap_end_apply, hsmul]
      change (hs.unit : X.presheaf.stalk x) • ((↑hs.unit⁻¹ : X.presheaf.stalk x) • m) = m
      rw [smul_smul, Units.mul_inv, one_smul]
  · -- surjectivity up to `p.primeCompl`
    obtain ⟨W, hxW, t, rfl⟩ := M.presheaf.exists_germ_eq m
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hx
    let : Module Γ(X, U) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
    have := Scheme.Modules.isLocalizedModule_basicOpen M hU f (fun _ _ => rfl)
      (resBasicOpen M f) (fun _ => rfl)
    obtain ⟨⟨n, s⟩, hns⟩ := IsLocalizedModule.surj (Submonoid.powers f) (resBasicOpen M f)
      (M.presheaf.map (homOfLE hfW).op t)
    refine ⟨⟨n, ⟨(s : Γ(X, U)), hpow f s hxf⟩⟩, ?_⟩
    have key := congrArg (M.presheaf.germ (X.basicOpen f) x hxf) hns
    simp only at key
    change M.presheaf.germ (X.basicOpen f) x hxf
      ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op (s : Γ(X, U))) •
        M.presheaf.map (homOfLE hfW).op t) =
      M.presheaf.germ (X.basicOpen f) x hxf (M.presheaf.map (homOfLE (X.basicOpen_le f)).op n)
      at key
    rw [germ_smul', TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply] at key
    change (s : Γ(X, U)) • M.presheaf.germ W x hxW t = g n
    rw [hsmul, hg]
    exact key
  · -- two sections with the same germ agree after multiplying by an element of `p.primeCompl`
    rw [hg, hg] at h
    obtain ⟨W, hxW, iU, iU', heq⟩ := M.presheaf.germ_eq x hx hx n n' h
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hx
    let : Module Γ(X, U) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
    have := Scheme.Modules.isLocalizedModule_basicOpen M hU f (fun _ _ => rfl)
      (resBasicOpen M f) (fun _ => rfl)
    have hres : resBasicOpen M f n = resBasicOpen M f n' := by
      change M.presheaf.map (homOfLE (X.basicOpen_le f)).op n =
        M.presheaf.map (homOfLE (X.basicOpen_le f)).op n'
      have e1 : (homOfLE (X.basicOpen_le f) : X.basicOpen f ⟶ U) = homOfLE hfW ≫ iU :=
        Subsingleton.elim _ _
      have e2 : (homOfLE (X.basicOpen_le f) : X.basicOpen f ⟶ U) = homOfLE hfW ≫ iU' :=
        Subsingleton.elim _ _
      conv_lhs => rw [e1]
      conv_rhs => rw [e2]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      rw [heq]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
      (f := resBasicOpen M f) hres
    refine ⟨⟨(c : Γ(X, U)), hpow f c hxf⟩, ?_⟩
    simpa [Submonoid.smul_def] using hc

end CoherentFreeStalksAux

open AlgebraicGeometry in
/-- **A coherent sheaf on a locally noetherian scheme whose stalks are all free is locally free**
(Stacks 0B8J, via Stacks 00NX). Proof: see the module docstring. -/
theorem AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_free_stalk {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (M : X.Modules) [M.IsCoherent]
    (h : ∀ x : X, Module.Free (X.presheaf.stalk x) (M.stalk x)) :
    M.IsLocallyFree := by
  have hqc : M.IsQuasicoherent := Scheme.Modules.IsCoherent.quasicoherent
  have hft : M.IsFiniteType := Scheme.Modules.IsCoherent.finiteType
  refine Scheme.Modules.isLocallyFree_of_free_affine_sections M fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (⊤ : X.Opens) from trivial)
  have hU : IsAffineOpen U := hU
  -- the local algebra: `A = Γ(X, U)`, `N = Γ(M, U)`, `p` the prime of `x`
  set p := hU.primeIdealOf ⟨x, hxU⟩ with hp
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  let modA : Module Γ(X, U) (M.presheaf.stalk x) :=
    Module.compHom (M.presheaf.stalk x) (X.presheaf.germ U x hxU).hom
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (M.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : Γ(M, U) →ₗ[Γ(X, U)] M.presheaf.stalk x :=
    { toFun := M.presheaf.germ U x hxU
      map_add' := map_add _
      map_smul' := fun r m => CoherentFreeStalksAux.germ_smul' M hxU r m }
  have : IsLocalizedModule p.asIdeal.primeCompl g :=
    CoherentFreeStalksAux.isLocalizedModule_germ M hU hxU (fun _ _ => rfl) g (fun _ => rfl)
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite Γ(X, U) Γ(M, U) := Scheme.Modules.finite_sections_of_isFiniteType M hU
  have : Module.FinitePresentation Γ(X, U) Γ(M, U) := Module.finitePresentation_of_finite _ _
  have hfreex : Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x) := h x
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl g (X.presheaf.stalk x)
  have hxr : x ∈ X.basicOpen r :=
    (X.mem_basicOpen r x hxU).mpr
      ((IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) p.asIdeal r).mpr hr)
  refine ⟨X.basicOpen r, hU.basicOpen r, hxr, ?_,
    Scheme.Modules.finite_sections_of_isFiniteType M (hU.basicOpen r)⟩
  -- transport freeness from `N_r` over `A_r` to `Γ(M, D(r))` over `Γ(X, D(r))`
  let modD : Module Γ(X, U) Γ(M, X.basicOpen r) :=
    Module.compHom Γ(M, X.basicOpen r) (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  have := Scheme.Modules.isLocalizedModule_basicOpen M hU r (fun _ _ => rfl)
    (CoherentFreeStalksAux.resBasicOpen M r) (fun _ => rfl)
  have : IsLocalization.Away r Γ(X, X.basicOpen r) := hU.isLocalization_basicOpen r
  let e₁ : Localization.Away r ≃ₐ[Γ(X, U)] Γ(X, X.basicOpen r) :=
    IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) Γ(X, X.basicOpen r)
  let e₂ : LocalizedModule.Away r Γ(M, U) ≃ₗ[Γ(X, U)] Γ(M, X.basicOpen r) :=
    IsLocalizedModule.iso (Submonoid.powers r) (CoherentFreeStalksAux.resBasicOpen M r)
  let σ : Localization.Away r ≃+* Γ(X, X.basicOpen r) := e₁.toRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  have hsm : ∀ (a : Localization.Away r) (m : LocalizedModule.Away r Γ(M, U)),
      e₂ (a • m) = σ a • e₂ m := by
    intro a m
    induction a using Localization.induction_on with
    | H y =>
      obtain ⟨n, s⟩ := y
      apply IsLocalizedModule.smul_injective (CoherentFreeStalksAux.resBasicOpen M r) s
      simp only
      have hl : (s : Γ(X, U)) • e₂ (Localization.mk n s • m) = (n : Γ(X, U)) • e₂ m := by
        rw [← e₂.map_smul, ← algebraMap_smul (Localization.Away r) (s : Γ(X, U)), smul_smul,
          Localization.mk_eq_mk', IsLocalization.mk'_spec', algebraMap_smul, e₂.map_smul]
      have hr' : (s : Γ(X, U)) • (σ (Localization.mk n s) • e₂ m) = (n : Γ(X, U)) • e₂ m := by
        change (algebraMap Γ(X, U) Γ(X, X.basicOpen r) (s : Γ(X, U))) • (σ (Localization.mk n s) • e₂ m) =
          (algebraMap Γ(X, U) Γ(X, X.basicOpen r) (n : Γ(X, U))) • e₂ m
        rw [smul_smul, ← e₁.commutes (s : Γ(X, U)), ← e₁.commutes n]
        change (e₁ (algebraMap Γ(X, U) (Localization.Away r) (s : Γ(X, U))) * e₁ (Localization.mk n s)) • e₂ m =
          e₁ (algebraMap Γ(X, U) (Localization.Away r) n) • e₂ m
        rw [← map_mul, Localization.mk_eq_mk', IsLocalization.mk'_spec']
      exact hl.trans hr'.symm
  let E : LocalizedModule.Away r Γ(M, U) ≃ₛₗ[(σ : Localization.Away r →+* Γ(X, X.basicOpen r))]
      Γ(M, X.basicOpen r) :=
    { toFun := e₂
      invFun := e₂.symm
      left_inv := e₂.left_inv
      right_inv := e₂.right_inv
      map_add' := e₂.map_add
      map_smul' := hsm }
  exact Module.Free.of_equiv E

end
