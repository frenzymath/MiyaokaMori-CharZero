import MiyaokaMori.Prelude

/-! # Epimorphisms and exactness of sheaves of modules via local lifting of sections

Statement: `X` a scheme. (1) A morphism of `O_X`-modules `φ : M → N` is an epimorphism (`Epi`) ⟺ it is
locally surjective on sections: for every open `U`, `s ∈ Γ(U, N)` and `p ∈ U` there are an open
`p ∈ V ⊆ U` and `y ∈ Γ(V, M)` with `φ_V(y) = s|_V`. (2) A short complex of `O_X`-modules
`S : X₁ →f X₂ →g X₃` (`g∘f = 0`) is exact ⟺ for every open `U`, `x ∈ Γ(U, X₂)` with `g_U(x) = 0` and
`p ∈ U`, there are an open `p ∈ V ⊆ U` and `y ∈ Γ(V, X₁)` with `f_V(y) = x|_V`. No quasi-coherence is needed.

Proof:
1. (Locally surjective ⇒ Epi) The forgetful functor `SheafOfModules.toSheaf` to sheaves of abelian groups
   is faithful, and faithful functors reflect epimorphisms; a locally surjective morphism of sheaves of
   abelian groups is an epimorphism (`TopCat.Sheaf.isLocallySurjective_iff_epi`,
   `TopCat.Presheaf.isLocallySurjective_iff`).
2. (Epi ⇒ locally surjective) Let `L ⊣ G` be the sheafification adjunction of presheaves of modules
   (`PresheafOfModules.sheafificationAdjunction (𝟙 O_X)`, `G` the forgetful functor, the counit an
   isomorphism). Take the presheaf cokernel `π : G N → Q = coker(G φ)`. From `G φ ≫ π = 0` we get
   `L(Gφ) ≫ Lπ = 0`; naturality of the counit gives `ε_M ≫ φ ≫ ε_N⁻¹ ≫ Lπ = 0`, and since `ε_M` is an
   isomorphism and `φ` an epimorphism, `Lπ = 0`; naturality of the unit gives `π ≫ η_Q = η ≫ G(Lπ) = 0`.
   The underlying morphism of presheaves of abelian groups of `η_Q` is `toSheafify`
   (`toPresheaf_map_sheafificationAdjunction_unit_app`), which is locally injective
   (`Presheaf.isLocallyInjective_toSheafify'`): for `s ∈ Γ(U, N)`, `η(π s) = 0 = η(0)` gives a covering
   sieve of `U` on which `π(s)|_V = 0`, i.e. `π_V(s|_V) = 0`. The evaluation functor
   `PresheafOfModules.evaluation V` preserves finite colimits, so `Γ(V, M) → Γ(V, N) → Q(V)` is exact
   (`Functor.preservesFiniteColimits_tfae`, `ShortComplex.moduleCat_exact_iff`), giving `y` with
   `φ_V(y) = s|_V`.
3. (Sections of the kernel) If `T` is exact and `T.f` mono, then the evaluation functor
   `SheafOfModules.evaluation U` preserves finite limits, so on every `U`, `T.f_U` is injective and
   `ker(T.g_U) ⊆ im(T.f_U)` (`Functor.preservesFiniteLimits_tfae`). Applied to `T = (S.iCycles, S.g)`
   (`ShortComplex.cyclesIsKernel`, `exact_of_f_is_kernel`).
4. (Proof of (2)) In an abelian category `S` is exact ⟺ `S.toCycles` is an epimorphism
   (`ShortComplex.exact_iff_epi_toCycles`), and `S.toCycles ≫ S.iCycles = S.f`. "⇒": from `g x = 0`,
   step 3 gives `x = i(z)`; by (1), `z` is locally `toCycles(y)`, so `x|_V = i(toCycles y) = f(y)`.
   "⇐": for `z ∈ Γ(U, cycles)`, `x = i(z)` satisfies `g x = 0`, locally `x|_V = f(y) = i(toCycles y)`,
   and `i_V` is injective (step 3), so `z|_V = toCycles(y)`; hence `toCycles` is locally surjective and
   an epimorphism by (1).

Reference: Stacks 01AG / 00WN (epimorphisms of sheaves = locally surjective; exactness is checked
locally / on stalks).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

namespace ModulesLocLiftAux

variable {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)

/-- Local surjectivity at the level of sections. -/
def LocSurj : Prop :=
  ∀ (U : X.Opens) (s : Γ(N, U)) (p : X), p ∈ U → ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
    ∃ y : Γ(M, V), φ.app V y = N.presheaf.map (homOfLE hVU).op s

theorem locSurj_iff :
    LocSurj φ ↔ TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  constructor
  · intro h U t x hx
    obtain ⟨V, hVU, hp, y, hy⟩ := h U t x hx
    exact ⟨V, hVU, ⟨y, hy⟩, hp⟩
  · intro h U s p hp
    obtain ⟨V, hVU, ⟨y, hy⟩, hpV⟩ := h U s p hp
    exact ⟨V, hVU, hpV, y, hy⟩

theorem epi_of_locSurj (h : LocSurj φ) : Epi φ := by
  have h1 := (locSurj_iff φ).mp h
  have : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp h1
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map this

theorem unit_comp_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) [IsIso adj.counit] [L.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] {M N : D} (φ : M ⟶ N) [Epi φ] {Q : C} (π : G.obj N ⟶ Q)
    (h : G.map φ ≫ π = 0) : π ≫ adj.unit.app Q = 0 := by
  have h1 : L.map (G.map φ) ≫ L.map π = 0 := by
    rw [← L.map_comp, h, L.map_zero]
  have h2 : L.map (G.map φ) ≫ adj.counit.app N = adj.counit.app M ≫ φ := adj.counit.naturality φ
  have h3 : (adj.counit.app M ≫ φ) ≫ (inv (adj.counit.app N) ≫ L.map π) = 0 := by
    rw [← h2, Category.assoc, IsIso.hom_inv_id_assoc, h1]
  have h4 : inv (adj.counit.app N) ≫ L.map π = 0 := by
    have : Epi (adj.counit.app M ≫ φ) := epi_comp _ _
    exact (cancel_epi (adj.counit.app M ≫ φ)).mp (by rw [h3, comp_zero])
  have hL : L.map π = 0 := by
    rw [← cancel_epi (inv (adj.counit.app N)), h4, comp_zero]
  have := adj.unit.naturality π
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at this
  rw [this, hL, G.map_zero, comp_zero]

theorem locSurj_of_epi [Epi φ] : LocSurj φ := by
  have hepi : Epi (C := SheafOfModules.{u} X.ringCatSheaf) φ := ‹Epi φ›
  have hη := unit_comp_eq_zero (D := SheafOfModules.{u} X.ringCatSheaf)
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)) φ
    (cokernel.π _) (cokernel.condition _)
  replace hη := congr((PresheafOfModules.toPresheaf _).map $hη)
  rw [Functor.map_comp, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app,
    Functor.map_zero] at hη
  intro U s p hp
  set ψ := (SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map φ with hψ
  let c : (cokernel ψ).presheaf.obj (op U) :=
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (cokernel.π ψ)).app (op U) s
  have hc : (toSheafify (Opens.grothendieckTopology ↥X) (cokernel ψ).presheaf).app (op U) c =
      (toSheafify (Opens.grothendieckTopology ↥X) (cokernel ψ).presheaf).app (op U) 0 := by
    rw [map_zero]
    exact congr(($hη).app (op U) s)
  obtain ⟨V, i, hi, hpV⟩ := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology ↥X)
    (toSheafify (Opens.grothendieckTopology ↥X) (cokernel ψ).presheaf) c 0 hc p hp
  refine ⟨V, leOfHom i, hpV, ?_⟩
  let S₀ : ShortComplex (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
    ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition ψ)
  have hS₀ : S₀.Exact ∧ Epi S₀.g := ⟨ShortComplex.exact_cokernel ψ, inferInstanceAs (Epi (cokernel.π ψ))⟩
  have h31 := (Functor.preservesFiniteColimits_tfae
    (PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op V))).out 3 1
  have hex := h31.mp inferInstance S₀ hS₀
  have hex' := (ShortComplex.moduleCat_exact_iff _).mp hex.1
  have hz : (cokernel.π ψ).app (op V) (N.presheaf.map (homOfLE (leOfHom i)).op s) = 0 := by
    have hi' : (cokernel ψ).presheaf.map i.op c = (cokernel ψ).presheaf.map i.op 0 := hi
    rw [map_zero] at hi'
    refine Eq.trans ?_ hi'
    exact congr($(((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (cokernel.π ψ)).naturality i.op) s)
  obtain ⟨y, hy⟩ := hex' _ hz
  exact ⟨y, hy⟩

variable {X : Scheme.{u}}
/-- The kernel at the level of sections: if `S` is exact and `S.f` is mono, then on every open `f` is
injective and `ker g ⊆ im f`. -/
theorem sections_of_exact_mono (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f] (U : X.Opens) :
    Function.Injective (S.f.app U) ∧
      ∀ x : Γ(S.X₂, U), S.g.app U x = 0 → ∃ z : Γ(S.X₁, U), S.f.app U z = x := by
  have hadd : (SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).Additive :=
    inferInstanceAs ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  have h31 := (Functor.preservesFiniteLimits_tfae
    (SheafOfModules.evaluation.{u} X.ringCatSheaf (op U))).out 3 1
  have hex := h31.mp inferInstance S ⟨hS, ‹Mono S.f›⟩
  have hex' := (ShortComplex.moduleCat_exact_iff _).mp hex.1
  have hmono := hex.2
  refine ⟨?_, fun x hx => ?_⟩
  · exact (ModuleCat.mono_iff_injective _).mp hmono
  · obtain ⟨z, hz⟩ := hex' x hx
    exact ⟨z, hz⟩

theorem exact_iff_locally_lift (S : ShortComplex X.Modules) :
    S.Exact ↔ ∀ (U : X.Opens) (x : Γ(S.X₂, U)), S.g.app U x = 0 → ∀ p : X, p ∈ U →
      ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
        ∃ y : Γ(S.X₁, V), S.f.app V y = S.X₂.presheaf.map (homOfLE hVU).op x := by
  let T : ShortComplex X.Modules := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel _ S.cyclesIsKernel
  have hTm : Mono T.f := inferInstanceAs (Mono S.iCycles)
  have hfac : ∀ (V : X.Opens) (y : Γ(S.X₁, V)), S.iCycles.app V (S.toCycles.app V y) = S.f.app V y :=
    fun V y => by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, S.toCycles_i]
  rw [S.exact_iff_epi_toCycles]
  constructor
  · intro hepi U x hx p hp
    obtain ⟨z, hz⟩ := (sections_of_exact_mono T hT U).2 x hx
    obtain ⟨V, hVU, hpV, y, hy⟩ := locSurj_of_epi S.toCycles U z p hp
    refine ⟨V, hVU, hpV, y, ?_⟩
    rw [← hfac, hy, ← hz]
    exact congr($(S.iCycles.mapPresheaf.naturality (homOfLE hVU).op) z)
  · intro h
    apply epi_of_locSurj
    intro U z p hp
    have hx : S.g.app U (S.iCycles.app U z) = 0 := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, S.iCycles_g]
      rfl
    obtain ⟨V, hVU, hpV, y, hy⟩ := h U _ hx p hp
    refine ⟨V, hVU, hpV, y, ?_⟩
    apply (sections_of_exact_mono T hT V).1
    change S.iCycles.app V _ = S.iCycles.app V _
    rw [hfac, hy]
    exact congr($(S.iCycles.mapPresheaf.naturality (homOfLE hVU).op) z).symm
end ModulesLocLiftAux

/-- An epimorphism of `O_X`-modules is the same as a morphism locally surjective on sections. -/
theorem AlgebraicGeometry.Scheme.Modules.epi_iff_locally_surjective_sections
    {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    CategoryTheory.Epi φ ↔ ∀ (U : X.Opens) (s : Γ(N, U)) (p : X), p ∈ U →
      ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
        ∃ y : Γ(M, V), φ.app V y = N.presheaf.map (homOfLE hVU).op s :=
  ⟨fun _ => ModulesLocLiftAux.locSurj_of_epi φ,
    fun h => ModulesLocLiftAux.epi_of_locSurj φ h⟩

/-- A short complex of `O_X`-modules is exact ⟺ sections of `ker g` locally come from `f`. -/
theorem AlgebraicGeometry.Scheme.Modules.exact_iff_locally_lift_sections
    {X : AlgebraicGeometry.Scheme.{u}} (S : CategoryTheory.ShortComplex X.Modules) :
    S.Exact ↔ ∀ (U : X.Opens) (x : Γ(S.X₂, U)), S.g.app U x = 0 → ∀ p : X, p ∈ U →
      ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
        ∃ y : Γ(S.X₁, V), S.f.app V y = S.X₂.presheaf.map (homOfLE hVU).op x :=
  ModulesLocLiftAux.exact_iff_locally_lift S

end
