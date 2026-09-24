import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks01xkSeparated
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks089w

/-! # Vanishing of cohomology is local on an affine base

Vanishing of `H^p(f⁻¹V, G)` is local on the base (Stacks 01XJ + 01XK made pointwise): `f : X → S`
quasi-compact and separated, `G` quasi-coherent on `X`, `p : ℕ`. If every point of `S` has an affine
open neighbourhood `W` with `H^p(f⁻¹W, G|_{f⁻¹W}) = 0`, then `H^p(f⁻¹V, G|_{f⁻¹V}) = 0` for **every**
affine open `V ⊆ S`.

This is the statement "`R^p f_* G` is a quasi-coherent sheaf on `S` (01XJ) whose sections over an
affine open `V` are `H^p(f⁻¹V, G)` (01XK); a quasi-coherent sheaf vanishing near every point is
zero". The library has no higher direct image object, so it is phrased on the cohomology groups.
Used for Stacks 02O1 (uniformity of `n₀` over all affine opens of a Noetherian base).

Source: Stacks 01XJ (coherent-lemma-quasi-coherence-higher-direct-images) (1), 01XK
(coherent-lemma-quasi-coherence-higher-direct-images-application); the separated case of 01XK is
`sheafCohomology_preimage_basicOpen_isLocalizedModule_of_isSeparated` (`Stacks01xkSeparated.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- `Subsingleton` of sheaf cohomology transports along an isomorphism of modules. -/
private theorem subsingleton_sheafH_of_iso_vlb {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) (p : ℕ)
    [hN : Subsingleton (CategoryTheory.Sheaf.H N.toAddCommGrpSheaf p)] :
    Subsingleton (CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p) := by
  refine ⟨fun x y => ?_⟩
  have hc : (SheafOfModules.toSheaf X.ringCatSheaf).map e.hom ≫
      (SheafOfModules.toSheaf X.ringCatSheaf).map e.inv = 𝟙 _ :=
    ((SheafOfModules.toSheaf X.ringCatSheaf).map_comp e.hom e.inv).symm.trans
      ((congrArg (SheafOfModules.toSheaf X.ringCatSheaf).map e.hom_inv_id).trans
        ((SheafOfModules.toSheaf X.ringCatSheaf).map_id M))
  have hround : ∀ z : CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p,
      z = Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) p
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) p z) := by
    intro z
    have h := Sheaf.H.map_comp_apply ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) z
    rw [hc] at h
    exact (Sheaf.H.map_id_apply z).symm.trans h
  rw [hround x, hround y,
    Subsingleton.elim (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) p x)
      (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) p y)]

/-- A localization of the zero module is zero. -/
private theorem subsingleton_of_isLocalizedModule_vlb {A : Type*} [CommRing A] (S : Submonoid A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (φ : M →ₗ[A] N) [IsLocalizedModule S φ] [Subsingleton M] : Subsingleton N := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S φ x
  obtain ⟨⟨m', s'⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S φ y
  simp only [Function.uncurry_apply_pair, Subsingleton.elim m 0, Subsingleton.elim m' 0,
    IsLocalizedModule.mk'_zero]

/-- A module whose localizations at finitely many elements generating the unit ideal all vanish is
zero (Stacks 00HN-style: `a_i^e • m = 0` for all `i` and `∑ c_i a_i^e = 1`). -/
private theorem subsingleton_of_isLocalizedModule_powers_span_vlb {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {ι : Type*} (t : Finset ι) (a : ι → A)
    (hspan : Ideal.span (a '' (t : Set ι)) = ⊤)
    (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]
    (φ : ∀ i, M →ₗ[A] N i) (hφ : ∀ i ∈ t, IsLocalizedModule (Submonoid.powers (a i)) (φ i))
    (hN : ∀ i ∈ t, Subsingleton (N i)) : Subsingleton M := by
  classical
  suffices hz : ∀ m : M, m = 0 from ⟨fun m₁ m₂ => (hz m₁).trans (hz m₂).symm⟩
  intro m
  have hk : ∀ i ∈ t, ∃ k : ℕ, a i ^ k • m = 0 := fun i hi => by
    haveI := hφ i hi
    haveI := hN i hi
    obtain ⟨⟨s', hs'⟩, hsm⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (a i)) (φ i)
      (m := m)).mp (Subsingleton.elim _ _)
    obtain ⟨k, rfl⟩ := hs'
    exact ⟨k, hsm⟩
  choose! k hk using hk
  have he : ∀ i ∈ t, a i ^ t.sup k • m = 0 := fun i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup hi : k i ≤ t.sup k)
    rw [hd, pow_add, mul_comm, mul_smul, hk i hi, smul_zero]
  have hI : Ideal.span ((fun x : A => x ^ t.sup k) '' (a '' (t : Set ι))) ≤
      LinearMap.ker (LinearMap.toSpanSingleton A M m) := by
    rw [Ideal.span_le]
    rintro r ⟨b, ⟨i, hi, rfl⟩, rfl⟩
    exact he i hi
  have h1 : (1 : A) ∈ Ideal.span ((fun x : A => x ^ t.sup k) '' (a '' (t : Set ι))) := by
    rw [Ideal.span_pow_eq_top _ hspan]
    trivial
  have := hI h1
  rwa [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply_one] at this

/-- `e_*(e^* N) ≅ N` for an isomorphism of schemes `e` (the pushforward along an isomorphism is an
equivalence, and the counit of `restrict ⊣ pushforward` is an isomorphism). -/
private def pushforwardRestrictIsoOfIso_vlb {U₁ U₂ : AlgebraicGeometry.Scheme.{u}} (e : U₁ ≅ U₂)
    (N : U₂.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pushforward e.hom).obj
      (AlgebraicGeometry.Scheme.Modules.restrict N e.hom) ≅ N :=
  let iA : AlgebraicGeometry.Scheme.Modules.pushforward e.inv ⋙
      AlgebraicGeometry.Scheme.Modules.pushforward e.hom ≅ 𝟭 _ :=
    AlgebraicGeometry.Scheme.Modules.pushforwardComp e.inv e.hom ≪≫
      AlgebraicGeometry.Scheme.Modules.pushforwardCongr e.inv_hom_id ≪≫
      AlgebraicGeometry.Scheme.Modules.pushforwardId U₂
  let r : AlgebraicGeometry.Scheme.Modules.restrict N e.hom ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward e.inv).obj N :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor e.hom).mapIso (iA.app N).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app
        ((AlgebraicGeometry.Scheme.Modules.pushforward e.inv).obj N)
  (AlgebraicGeometry.Scheme.Modules.pushforward e.hom).mapIso r ≪≫ iA.app N

/-- Sheaf cohomology transports along an isomorphism of schemes: if `H^p(U₂, N) = 0` then
`H^p(U₁, e^* N) = 0` (through Stacks 089W for the affine morphism `e.hom` and the isomorphism
`e_* e^* N ≅ N`). -/
private theorem subsingleton_sheafH_restrict_of_iso_vlb {U₁ U₂ : AlgebraicGeometry.Scheme.{u}}
    (e : U₁ ≅ U₂) (N : U₂.Modules) [N.IsQuasicoherent] (p : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H N.toAddCommGrpSheaf p)] :
    Subsingleton (CategoryTheory.Sheaf.H
      (AlgebraicGeometry.Scheme.Modules.restrict N e.hom).toAddCommGrpSheaf p) := by
  obtain ⟨ψ⟩ := AlgebraicGeometry.sheafCohomology_pushforward_equiv_of_isAffineHom e.hom
    (AlgebraicGeometry.Scheme.Modules.restrict N e.hom) p
  haveI := subsingleton_sheafH_of_iso_vlb (pushforwardRestrictIsoOfIso_vlb e N) p
  exact ψ.injective.subsingleton

section Opens

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/-- The morphism `f⁻¹V → V ≅ Spec Γ(S, V)` for an affine open `V ⊆ S`. -/
private noncomputable def toSpecOfAffineOpen_vlb (V : S.affineOpens) :
    (f ⁻¹ᵁ V.1).toScheme ⟶ AlgebraicGeometry.Spec (CommRingCat.of Γ(S, V.1)) :=
  (f ∣_ V.1) ≫ V.1.toSpecΓ

/-- The open `g_V⁻¹ D(a)` of `f⁻¹V`, in the form used by Stacks 01XK. -/
private noncomputable abbrev preimageBasicOpen_vlb (V : S.affineOpens) (a : Γ(S, V.1)) :
    (f ⁻¹ᵁ V.1).toScheme.Opens :=
  toSpecOfAffineOpen_vlb f V ⁻¹ᵁ (AlgebraicGeometry.Spec (CommRingCat.of Γ(S, V.1))).basicOpen
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Γ(S, V.1))).inv.hom a)

/-- `g_V⁻¹ D(a)`, viewed in `X`, is `f⁻¹(S.basicOpen a)`. -/
private theorem opensRange_preimageBasicOpen_vlb (V : S.affineOpens) (a : Γ(S, V.1)) :
    ((preimageBasicOpen_vlb f V a).ι ≫ (f ⁻¹ᵁ V.1).ι).opensRange = f ⁻¹ᵁ S.basicOpen a := by
  rw [AlgebraicGeometry.Scheme.Hom.opensRange_comp, AlgebraicGeometry.Scheme.Opens.opensRange_ι]
  have h1 : preimageBasicOpen_vlb f V a = (f ∣_ V.1) ⁻¹ᵁ (V.1.ι ⁻¹ᵁ S.basicOpen a) := by
    unfold preimageBasicOpen_vlb toSpecOfAffineOpen_vlb
    rw [AlgebraicGeometry.Scheme.Hom.comp_preimage, AlgebraicGeometry.basicOpen_eq_of_affine,
      AlgebraicGeometry.Scheme.Opens.toSpecΓ_preimage_basicOpen]
  rw [h1, AlgebraicGeometry.image_morphismRestrict_preimage,
    AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.Scheme.Opens.opensRange_ι, inf_eq_right.mpr (S.basicOpen_le a)]

end Opens

/-- Variant with the annihilation hypothesis stated pointwise. -/
private theorem subsingleton_of_pow_smul_eq_zero_span_vlb {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {ι : Type*} (t : Finset ι) (a : ι → A)
    (hspan : Ideal.span (a '' (t : Set ι)) = ⊤)
    (hann : ∀ i ∈ t, ∀ m : M, ∃ k : ℕ, a i ^ k • m = 0) : Subsingleton M := by
  classical
  suffices hz : ∀ m : M, m = 0 from ⟨fun m₁ m₂ => (hz m₁).trans (hz m₂).symm⟩
  intro m
  choose! k hk using fun i hi => hann i hi m
  have he : ∀ i ∈ t, a i ^ t.sup k • m = 0 := fun i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup hi : k i ≤ t.sup k)
    rw [hd, pow_add, mul_comm, mul_smul, hk i hi, smul_zero]
  have hI : Ideal.span ((fun x : A => x ^ t.sup k) '' (a '' (t : Set ι))) ≤
      LinearMap.ker (LinearMap.toSpanSingleton A M m) := by
    rw [Ideal.span_le]
    rintro r ⟨b, ⟨i, hi, rfl⟩, rfl⟩
    exact he i hi
  have h1 : (1 : A) ∈ Ideal.span ((fun x : A => x ^ t.sup k) '' (a '' (t : Set ι))) := by
    rw [Ideal.span_pow_eq_top _ hspan]
    trivial
  have := hI h1
  rwa [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply_one] at this

section Instances

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

private instance quasiCompact_toSpecOfAffineOpen_vlb [AlgebraicGeometry.QuasiCompact f]
    (V : S.affineOpens) : AlgebraicGeometry.QuasiCompact (toSpecOfAffineOpen_vlb f V) := by
  haveI : IsIso V.1.toSpecΓ := (inferInstance : IsIso V.2.isoSpec.hom)
  unfold toSpecOfAffineOpen_vlb
  infer_instance

private instance isSeparated_toSpecOfAffineOpen_vlb [AlgebraicGeometry.IsSeparated f]
    (V : S.affineOpens) : AlgebraicGeometry.IsSeparated (toSpecOfAffineOpen_vlb f V) := by
  haveI : IsIso V.1.toSpecΓ := (inferInstance : IsIso V.2.isoSpec.hom)
  haveI : AlgebraicGeometry.IsSeparated (f ∣_ V.1) :=
    AlgebraicGeometry.IsZariskiLocalAtTarget.restrict (P := @AlgebraicGeometry.IsSeparated)
      inferInstance V.1
  unfold toSpecOfAffineOpen_vlb
  infer_instance

end Instances

end AlgebraicGeometry.Scheme.Modules

/-- **Vanishing of cohomology is local on an affine base** (Stacks 01XJ(1) + 01XK, pointwise form). The
Lean proof follows the natural-language proof below step by step; the private helpers above are items
(i)–(iii). `f : X → S` quasi-compact and separated, `G` quasi-coherent, `p : ℕ`. If every `s : S` has an
affine open neighbourhood `W` with `H^p(f⁻¹W, G|_{f⁻¹W}) = 0`, then `H^p(f⁻¹V, G|_{f⁻¹V}) = 0` for every
affine open `V ⊆ S`. (Here `f⁻¹V` is the open subscheme `(f ⁻¹ᵁ V).toScheme` of `X` and `G|_{f⁻¹V}` is
Mathlib's `Scheme.Modules.restrict` along its inclusion `(f ⁻¹ᵁ V).ι`.)

**Natural-language proof (self-contained).** Fix an affine open `V`, write `A := Γ(S, V)`,
`X_V := f⁻¹V`, `g_V : X_V → Spec A` for `(f ∣_ V) ≫ hV.isoSpec.hom` (Mathlib `morphismRestrict`,
`IsAffineOpen.isoSpec`), and `M := H^p(X_V, G|_{X_V})`, an `A`-module through `g_V`
(`sheafCohomology.moduleOver` with `letI : X_V.Over (Spec A) := ⟨g_V⟩`). `g_V` is quasi-compact
and separated: `f ∣_ V` is the base change of `f` along `V.ι` (Mathlib `isPullback_morphismRestrict`;
`QuasiCompact` and `IsSeparated` are stable under base change and hold for isomorphisms).
1. *Basic opens adapted to two affines* (Mathlib `exists_basicOpen_le_affine_inter`): for `s ∈ V`
   choose by hypothesis an affine open `W_s ∋ s` with `H^p(f⁻¹W_s, G|) = 0`; then there are
   `a_s ∈ A = Γ(S, V)` and `b_s ∈ Γ(S, W_s)` with `S.basicOpen a_s = S.basicOpen b_s =: D_s`, `s ∈ D_s`
   (so `D_s ⊆ V ∩ W_s`).
2. *Finitely many suffice*: `V` is quasi-compact (affine, Mathlib `IsAffineOpen.isCompact`), so
   `V = D_{s_1} ∪ … ∪ D_{s_r}`; by Mathlib `IsAffineOpen.basicOpen_union_eq_self_iff`,
   `Ideal.span {a_{s_1}, …, a_{s_r}} = ⊤` in `A`.
3. *01XK for `V`* (`sheafCohomology_preimage_basicOpen_isLocalizedModule_of_isSeparated` applied to
   `g_V`, `G|_{X_V}`, `a_{s_i}`): the restriction map `M → H^p(g_V⁻¹D(a_{s_i}), G|)` is a localization of
   `A`-modules at the powers of `a_{s_i}`. Here `g_V⁻¹ D(a_{s_i})` is the open `f⁻¹D_{s_i}` of `X_V`
   (Mathlib `Scheme.toSpecΓ_preimage_basicOpen`: `hV.isoSpec.hom ⁻¹ᵁ D(a) = V.basicOpen a` transported
   to `V`, and `(f ∣_ V) ⁻¹ᵁ` of it is `f ⁻¹ᵁ (S.basicOpen a_{s_i})` viewed inside `X_V`,
   Mathlib `morphismRestrict_preimage`/`Scheme.Opens.ι_preimage`-type lemmas).
4. *01XK for `W_{s_i}`*: the same theorem for `g_{W_{s_i}} : f⁻¹W_{s_i} → Spec Γ(S, W_{s_i})` and `b_{s_i}`
   shows that `H^p(g_W⁻¹D(b_{s_i}), G|)` is a localization of `H^p(f⁻¹W_{s_i}, G|) = 0`, hence zero
   (a localization of the zero module is zero: every element is `mk' (φ m) t` with `m = 0`,
   Mathlib `IsLocalizedModule.mk'_surjective`).
5. *Two presentations of `f⁻¹D_{s_i}`*: the schemes `g_V⁻¹D(a_{s_i})` (open of `X_V`) and
   `g_W⁻¹D(b_{s_i})` (open of `f⁻¹W_{s_i}`) are both open subschemes of `X` with the same underlying open
   `f ⁻¹ᵁ D_{s_i}`, hence isomorphic over `X` (Mathlib `IsOpenImmersion.isoOfRangeEq`), and the two
   restrictions of `G` correspond under this isomorphism (`Scheme.Modules.restrictFunctorComp`,
   `restrictFunctorCongr`-type identification, since `j₁ = e.hom ≫ j₂`). Sheaf cohomology is
   invariant under an isomorphism of schemes with a compatible isomorphism of modules: `Sheaf.H` is
   `Ext^p(ℤ, -)` in the abelian category of abelian sheaves on the space, and an isomorphism of ringed
   spaces induces an equivalence of these abelian categories carrying the unit `ℤ` to `ℤ` (Mathlib:
   `Ext` is compatible with equivalences of abelian categories through `Functor.mapExt`; alternatively
   pushforward along an isomorphism preserves injectives and is exact, so `H^p(U₁, M) ≅ H^p(U₂, e_* M)`
   as for closed immersions in `ClosedSubspaceCohomology.lean`). Hence
   `H^p(g_V⁻¹D(a_{s_i}), G|) ≅ H^p(g_W⁻¹D(b_{s_i}), G|) = 0` (step 4).
6. *Algebra*: `M_{a_{s_i}} = 0` for all `i` (steps 3, 5) and `Ideal.span {a_{s_i}} = ⊤` (step 2) force
   `M = 0`: for `m ∈ M` and each `i`, `IsLocalizedModule.eq_zero_iff` gives `e_i` with
   `a_{s_i}^{e_i} • m = 0`; with `e := max e_i`, `Ideal.span {a_{s_i}^e} = ⊤` (Mathlib
   `Ideal.span_pow_eq_top`), so `1 = ∑ c_i a_{s_i}^e` and `m = ∑ c_i • a_{s_i}^e • m = 0`.
   `M` is `H^p(X_V, G|_{X_V})` as a set, so the latter is `Subsingleton`.

**Helpers used** (private, this module): (i) `subsingleton_sheafH_restrict_of_iso_vlb` — transport of
sheaf cohomology along an isomorphism of schemes, through Stacks 089W
(`sheafCohomology_pushforward_equiv_of_isAffineHom`: an isomorphism is an affine morphism) and the
isomorphism `e_* e^* N ≅ N` (`pushforwardRestrictIsoOfIso_vlb`); (ii) `opensRange_preimageBasicOpen_vlb`
— `g_V⁻¹ D(a)` viewed in `X` is `f ⁻¹ᵁ (S.basicOpen a)` (Mathlib `Opens.toSpecΓ_preimage_basicOpen`,
`image_morphismRestrict_preimage`); (iii) `subsingleton_of_pow_smul_eq_zero_span_vlb` — the algebra
of step 6. The 01XK input is `Stacks01xkSeparated.lean`.

**Edge cases.** `V = ⊥`: `A = 0`, `M` is a module over the zero ring, hence zero — consistent
(alternatively `f⁻¹∅ = ∅`, whose cohomology vanishes). `S = ∅`: vacuous. `p = 0`: the statement says
`Γ(f⁻¹V, G) = 0` for all affine `V` when it vanishes near every point — true (sections of `f_*G`,
a sheaf). `X = ∅`: all groups zero. -/
theorem AlgebraicGeometry.sheafCohomology_restrict_preimage_subsingleton_of_forall_exists_affineOpen
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsSeparated f]
    (G : X.Modules) [G.IsQuasicoherent] (p : ℕ)
    (h : ∀ s : S, ∃ W : S.affineOpens, s ∈ W.1 ∧
      Subsingleton (CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.restrict G (f ⁻¹ᵁ W.1).ι).toAddCommGrpSheaf p)) :
    ∀ V : S.affineOpens,
      Subsingleton (CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.restrict G (f ⁻¹ᵁ V.1).ι).toAddCommGrpSheaf p) := by
  classical
  intro V
  -- Step 1: for every point of `V`, a basic open `D(a) = D(b)` inside `V ∩ W` with `H^p(f⁻¹W, G) = 0`.
  have hpt : ∀ x : V.1, ∃ (W : S.affineOpens) (a : Γ(S, V.1)) (b : Γ(S, W.1)),
      S.basicOpen a = S.basicOpen b ∧ (x : S) ∈ S.basicOpen a ∧
      Subsingleton (CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.restrict G (f ⁻¹ᵁ W.1).ι).toAddCommGrpSheaf p) := by
    intro x
    obtain ⟨W, hxW, hW⟩ := h x
    obtain ⟨a, b, hab, hxa⟩ :=
      AlgebraicGeometry.exists_basicOpen_le_affine_inter V.2 W.2 x ⟨x.2, hxW⟩
    exact ⟨W, a, b, hab, hxa, hW⟩
  choose W a b hab hxa hW using hpt
  -- Step 2: finitely many of them cover `V`, so the `a x` generate the unit ideal of `Γ(S, V)`.
  obtain ⟨t, ht⟩ := V.2.isCompact.elim_finite_subcover
    (fun x : V.1 => (S.basicOpen (a x) : Set S)) (fun x => (S.basicOpen (a x)).isOpen)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxa ⟨y, hy⟩⟩)
  have hspan : Ideal.span (a '' ↑t) = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact Opens.mem_iSup.mpr ⟨⟨a x, x, hxt, rfl⟩, hyx⟩
  -- Step 3: `H^p(f⁻¹V, G)` as a `Γ(S, V)`-module through `g_V : f⁻¹V → Spec Γ(S, V)`.
  letI : (f ⁻¹ᵁ V.1).toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of Γ(S, V.1))) :=
    ⟨AlgebraicGeometry.Scheme.Modules.toSpecOfAffineOpen_vlb f V⟩
  suffices hM : Subsingleton (AlgebraicGeometry.sheafCohomology (f ⁻¹ᵁ V.1)
      (AlgebraicGeometry.Scheme.Modules.restrict G (f ⁻¹ᵁ V.1).ι) p) from hM
  refine AlgebraicGeometry.Scheme.Modules.subsingleton_of_pow_smul_eq_zero_span_vlb t a hspan
    (fun x hxt m => ?_)
  -- Step 4: `H^p(g_W⁻¹D(b x), G) = 0` (localization of `H^p(f⁻¹W, G) = 0`, Stacks 01XK for `W`).
  letI : (f ⁻¹ᵁ (W x).1).toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of Γ(S, (W x).1))) :=
    ⟨AlgebraicGeometry.Scheme.Modules.toSpecOfAffineOpen_vlb f (W x)⟩
  letI : (AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f (W x) (b x)).toScheme.Over
      (AlgebraicGeometry.Spec (CommRingCat.of Γ(S, (W x).1))) :=
    ⟨(AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f (W x) (b x)).ι ≫
      AlgebraicGeometry.Scheme.Modules.toSpecOfAffineOpen_vlb f (W x)⟩
  letI : (AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f V (a x)).toScheme.Over
      (AlgebraicGeometry.Spec (CommRingCat.of Γ(S, V.1))) :=
    ⟨(AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f V (a x)).ι ≫
      AlgebraicGeometry.Scheme.Modules.toSpecOfAffineOpen_vlb f V⟩
  haveI : Subsingleton (AlgebraicGeometry.sheafCohomology (f ⁻¹ᵁ (W x).1)
      (AlgebraicGeometry.Scheme.Modules.restrict G (f ⁻¹ᵁ (W x).1).ι) p) := hW x
  obtain ⟨ψ, hψ⟩ := AlgebraicGeometry.sheafCohomology_preimage_basicOpen_isLocalizedModule_of_isSeparated
    (AlgebraicGeometry.Scheme.Modules.toSpecOfAffineOpen_vlb f (W x))
    (AlgebraicGeometry.Scheme.Modules.restrict G (f ⁻¹ᵁ (W x).1).ι) (b x) p
  haveI := hψ
  haveI hNW := AlgebraicGeometry.Scheme.Modules.subsingleton_of_isLocalizedModule_vlb
    (Submonoid.powers (b x)) ψ
  -- Step 5: the two presentations of `f⁻¹D` are isomorphic over `X`; transport the vanishing.
  have hr : Set.range ((AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f V (a x)).ι ≫
        (f ⁻¹ᵁ V.1).ι) =
      Set.range ((AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f (W x) (b x)).ι ≫
        (f ⁻¹ᵁ (W x).1).ι) := by
    have h1 := AlgebraicGeometry.Scheme.Modules.opensRange_preimageBasicOpen_vlb f V (a x)
    have h2 := AlgebraicGeometry.Scheme.Modules.opensRange_preimageBasicOpen_vlb f (W x) (b x)
    rw [hab x] at h1
    exact congrArg (fun U : X.Opens => (U : Set X)) (h1.trans h2.symm)
  let e := AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq _ _ hr
  have hfac := AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr
  let N := (AlgebraicGeometry.Scheme.Modules.restrict G (f ⁻¹ᵁ (W x).1).ι).restrict
    (AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f (W x) (b x)).ι
  haveI : Subsingleton (CategoryTheory.Sheaf.H N.toAddCommGrpSheaf p) := hNW
  haveI := AlgebraicGeometry.Scheme.Modules.subsingleton_sheafH_restrict_of_iso_vlb e N p
  let i : (AlgebraicGeometry.Scheme.Modules.restrict G (f ⁻¹ᵁ V.1).ι).restrict
      (AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f V (a x)).ι ≅ N.restrict e.hom :=
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorComp
        (AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f V (a x)).ι (f ⁻¹ᵁ V.1).ι).app G).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr hfac.symm).app G ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorComp e.hom
        ((AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f (W x) (b x)).ι ≫
          (f ⁻¹ᵁ (W x).1).ι)).app G ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor e.hom).mapIso
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctorComp
          (AlgebraicGeometry.Scheme.Modules.preimageBasicOpen_vlb f (W x) (b x)).ι
          (f ⁻¹ᵁ (W x).1).ι).app G)
  haveI hUV := AlgebraicGeometry.Scheme.Modules.subsingleton_sheafH_of_iso_vlb i p
  -- Step 6: Stacks 01XK for `V`: `H^p(g_V⁻¹D(a x), G)` is the localization of `M` at `a x`; it is zero.
  obtain ⟨φ, hφ⟩ := AlgebraicGeometry.sheafCohomology_preimage_basicOpen_isLocalizedModule_of_isSeparated
    (AlgebraicGeometry.Scheme.Modules.toSpecOfAffineOpen_vlb f V)
    (AlgebraicGeometry.Scheme.Modules.restrict G (f ⁻¹ᵁ V.1).ι) (a x) p
  haveI := hφ
  obtain ⟨⟨s', hs'⟩, hsm⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (a x)) φ
    (m := m)).mp (@Subsingleton.elim _ hUV _ _)
  obtain ⟨k, rfl⟩ := hs'
  exact ⟨k, hsm⟩

end
