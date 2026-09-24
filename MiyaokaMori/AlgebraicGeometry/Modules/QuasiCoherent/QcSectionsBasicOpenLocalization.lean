import MiyaokaMori.Prelude

/-! # Sections of a quasi-coherent sheaf on a basic open

Let `X` be a scheme, `M` a quasi-coherent `O_X`-module, `U ⊆ X` an affine open, `h ∈ Γ(U, O_X)` and
`D(h) = X.basicOpen h ⊆ U`. Then the restriction map `Γ(U, M) → Γ(D(h), M)` has the two properties of
"localization at `h`": (a) (existence) for every `s ∈ Γ(D(h), M)` there are `n` and `t ∈ Γ(U, M)` with
`t|_{D(h)} = (h|_{D(h)})^n • s`; (b) (uniqueness) if `t ∈ Γ(U, M)` satisfies `t|_{D(h)} = 0`, then
`h^n • t = 0` for some `n`.

Proof:
1. (On `Spec`) Let `R` be a ring, `N` a quasi-coherent sheaf on `Spec R` and `f ∈ R`. Mathlib's
   `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent` gives `Γ(N)^~ ≅ N`, and
   `isIso_fromTildeΓ_iff_isLocalizing` translates this into: the restriction `Γ(Spec R, N) → Γ(D(f), N)`
   is the localization of `R`-modules at the powers of `f` (`IsLocalizedModule.Away f`). Surjectivity of
   the localization (`IsLocalizedModule.Away.surj`) gives (a) and `IsLocalizedModule.eq_zero_iff` gives (b).
2. (Transport) Let `A = Γ(U, O_X)`, `j = hU.fromSpec : Spec A → X` (an open immersion with image `U`),
   `N = M.restrict j`, quasi-coherent (Mathlib `isQuasicoherent_restrictFunctor`). For `V ⊆ Spec A` open,
   `Γ(V, N) = Γ(j(V), M)` (`restrictAppIso`, the identity by definition); `j(⊤) = U`
   (`opensRange_fromSpec`) and `j(D(h)) = X.basicOpen h` (`IsAffineOpen.fromSpec_image_basicOpen`).
3. (Compatibility of scalars) The action of `A` on `Γ(V, N)` (`smul_Spec_def`: through `ΓSpecIso⁻¹` and
   restriction to `V`) equals the action `r ↦ (r|_{j(V)}) • −` on `Γ(j(V), M)`. This reduces to the
   ring-homomorphism identity `ΓSpecIso⁻¹ ≫ res_V ≫ (j.appIso V)⁻¹ = res^U_{j(V)}`, which follows from
   `IsAffineOpen.fromSpec_app_self` (`ΓSpecIso⁻¹ ≫ res = j.appLE U V`) and `Scheme.Hom.appLE_appIso_inv`.
4. Apply step 1 to `N` and `f = h`, and transport sections and scalars back to `M` by steps 2 and 3 to get
   (a) and (b) (composites of restriction maps are unique in a preorder category, and restriction along an
   `eqToHom` is bijective).

Source: Stacks 01I8 / 01IB (a quasi-coherent sheaf on an affine scheme is `M~`, with `Γ(D(f), M~) = M_f`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

namespace QcBasicOpenLocAux

variable {R : CommRingCat.{u}} (N : (Spec R).Modules) [N.IsQuasicoherent]

/-- `D(f)` as an open subset of `Spec R`. -/
abbrev D (f : R) : (Spec R).Opens := PrimeSpectrum.basicOpen f

theorem spec_exists (f : R) (s : Γ(N, D f)) :
    ∃ (n : ℕ) (t : Γ(N, ⊤)), N.presheaf.map (homOfLE (le_top : D f ≤ ⊤)).op t = f ^ n • s := by
  have h : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj N).obj.map (D f).leTop.op).hom :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance f
  obtain ⟨n, y, hy⟩ := h.surj _ _ s
  exact ⟨n, y, hy.symm⟩

theorem spec_unique (f : R) (t : Γ(N, ⊤))
    (ht : N.presheaf.map (homOfLE (le_top : D f ≤ ⊤)).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  have h : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj N).obj.map (D f).leTop.op).hom :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance f
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f)
    ((modulesSpecToSheaf.obj N).obj.map (D f).leTop.op).hom).mp ht
  exact ⟨n, hn⟩
variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

theorem image_le (V : (Spec Γ(X, U)).Opens) : hU.fromSpec ''ᵁ V ≤ U := by
  have := Scheme.Hom.image_le_opensRange hU.fromSpec V
  rwa [hU.opensRange_fromSpec] at this

theorem ring_key (V : (Spec Γ(X, U)).Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op ≫
      (hU.fromSpec.appIso V).inv = X.presheaf.map (homOfLE (image_le hU V)).op := by
  have h1 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op =
      hU.fromSpec.appLE U V (by rw [hU.fromSpec_preimage_self]; exact le_top) := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rfl
  rw [← Category.assoc, h1, Scheme.Hom.appLE_appIso_inv]
variable (M : X.Modules)

theorem smul_key (V : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) (x : Γ(M.restrict hU.fromSpec, V)) :
    r • x = (M.restrictAppIso hU.fromSpec V).inv
      ((X.presheaf.map (homOfLE (image_le hU V)).op r) • (M.restrictAppIso hU.fromSpec V).hom x) := by
  rw [Scheme.Modules.smul_Spec_def, ← ring_key hU V]
  rfl


theorem image_top : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

include hU in
theorem exists_lift [M.IsQuasicoherent] (h : Γ(X, U)) (s : Γ(M, X.basicOpen h)) :
    ∃ (n : ℕ) (t : Γ(M, U)), M.presheaf.map (homOfLE (X.basicOpen_le h)).op t =
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) ^ n • s := by
  have e1 : hU.fromSpec ''ᵁ D h = X.basicOpen h := hU.fromSpec_image_basicOpen h
  obtain ⟨n, t', ht⟩ := spec_exists (M.restrict hU.fromSpec) h
    ((M.restrictAppIso hU.fromSpec _).inv (M.presheaf.map (eqToHom e1).op s))
  refine ⟨n, M.presheaf.map (eqToHom (image_top hU).symm).op ((M.restrictAppIso hU.fromSpec ⊤).hom t'), ?_⟩
  rw [smul_key] at ht
  replace ht := congr((M.restrictAppIso hU.fromSpec (D h)).hom $ht)
  rw [Scheme.Modules.map_restrictAppIso_hom_apply, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at ht
  have hinj : Function.Injective (M.presheaf.map (eqToHom e1).op) :=
    (ConcreteCategory.bijective_of_isIso _).injective
  apply hinj
  rw [Scheme.Modules.map_smul, ← map_pow, ← X.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply,
    ← M.presheaf.map_comp_apply]
  exact ht

include hU in
theorem exists_pow_smul_eq_zero [M.IsQuasicoherent] (h : Γ(X, U)) (t : Γ(M, U))
    (ht : M.presheaf.map (homOfLE (X.basicOpen_le h)).op t = 0) : ∃ n : ℕ, h ^ n • t = 0 := by
  have e1 : hU.fromSpec ''ᵁ D h = X.basicOpen h := hU.fromSpec_image_basicOpen h
  obtain ⟨n, hn⟩ := spec_unique (M.restrict hU.fromSpec) h
    ((M.restrictAppIso hU.fromSpec _).inv (M.presheaf.map (eqToHom (image_top hU)).op t)) (by
      apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec (D h)).hom).injective
      rw [Scheme.Modules.map_restrictAppIso_hom_apply, Iso.inv_hom_id_apply, map_zero,
        ← M.presheaf.map_comp_apply]
      have := congr(M.presheaf.map (eqToHom e1).op $ht)
      rw [← M.presheaf.map_comp_apply, map_zero] at this
      exact this)
  refine ⟨n, ?_⟩
  rw [smul_key] at hn
  replace hn := congr((M.restrictAppIso hU.fromSpec ⊤).hom $hn)
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, map_zero] at hn
  have hinj : Function.Injective (M.presheaf.map (eqToHom (image_top hU)).op) :=
    (ConcreteCategory.bijective_of_isIso _).injective
  apply hinj
  rw [map_zero, Scheme.Modules.map_smul]
  exact hn
end QcBasicOpenLocAux

/-- For a quasi-coherent sheaf on an affine open `U`: a section on `D(h)`, multiplied by some power of `h`,
lifts to `U` (surjectivity of the localization). -/
theorem AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map_basicOpen
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (h : Γ(X, U)) (s : Γ(M, X.basicOpen h)) :
    ∃ (n : ℕ) (t : Γ(M, U)), M.presheaf.map (homOfLE (X.basicOpen_le h)).op t =
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) ^ n • s :=
  QcBasicOpenLocAux.exists_lift hU M h s

/-- For a quasi-coherent sheaf on an affine open `U`: a section whose restriction to `D(h)` vanishes is
killed by some power of `h` (the kernel of the localization). -/
theorem AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (h : Γ(X, U)) (t : Γ(M, U))
    (ht : M.presheaf.map (homOfLE (X.basicOpen_le h)).op t = 0) : ∃ n : ℕ, h ^ n • t = 0 :=
  QcBasicOpenLocAux.exists_pow_smul_eq_zero hU M h t ht

end
