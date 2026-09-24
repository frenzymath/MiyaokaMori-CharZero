import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentialsLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualRestrictOpen
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFreeSheafFree
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeTangentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackCommute
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackRank
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaFiniteType
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01b6
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaOpenImmersionSquare
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerFiniteFree

/-! # Sections of `s^*Ω_{Z/C}` on a trivializing open are free

Sections of `s^*Ω_{Z/C}` over an open `U` on which `E = s^*T_{Z/C}` is trivial are a free
`Γ(U)`-module of rank `n+1`.

Setting (§2.2 of the paper): `p : Z ⟶ C` with a section `s`, an open
`Zx ⊆ Z` containing `s(C)` on which `p` is smooth of relative dimension `n+1`, and an open
`U ⊆ C` with `(s^*T_{Z/C})|_U ≅ O_U^{n+1}`. Conclusion: `Γ(U, (s^*Ω_{Z/C})|_U)` has a
`Γ(U, ⊤)`-basis indexed by `Fin (n+1)`.

Proof (Stacks 01US, 01CM; see `ConeTangentBundleLocalFrame` for the same factorisation).
1. `s` factors through `Zx`: `s = s' ≫ Zx.ι` (`hsZx`). With `q := Zx.ι ≫ p`,
   `Ω_{Z/C}|_{Zx} ≅ Ω_{Zx/C}` (01US, `Omega.restrictIso`), so `s^*Ω_{Z/C} ≅ G := s'^*Ω_{Zx/C}`
   and `E = s^*T_{Z/C} ≅ s'^*T_{Zx/C}` (`dual_restrict`, `pullbackComp`, `pullbackCongr`).
2. `Ω_{Zx/C}` is locally free of finite type (`q` smooth), hence so is `G`
   (`isLocallyFree_pullback`, `isFiniteType_pullback`).
3. Dual commutes with pullback for locally free finite type modules (`dual_pullback`):
   `G^∨ ≅ s'^*(Ω_{Zx/C}^∨) = s'^*T_{Zx/C} ≅ E`; and `G ≅ G^∨∨` (`dual_dual`), so
   `s^*Ω_{Z/C} ≅ G ≅ G^∨∨ ≅ E^∨`.
4. Restrict to `U`: `(s^*Ω_{Z/C})|_U ≅ (E^∨)|_U ≅ (E|_U)^∨` (`dual_restrict`) `≅ (O_U^{n+1})^∨`
   (`htriv`) `≅ O_U^{n+1}` (`dual_free_iso`).
5. Take global sections: an isomorphism of sheaves of modules on `U` induces a
   `Γ(U, ⊤)`-linear isomorphism on `Γ(-, ⊤)` (`SheafOfModules.evaluation`), and
   `Γ(U, O_U^{n+1})` has the standard basis (`MiyaokaMori.ExteriorPowerFiniteFree.finiteFreeSectionBasis`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem etaleChart_omega_sections_free {C Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C)
    (s : C ⟶ Z) (Zx : Z.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ p)] (U : C.Opens)
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.relativeTangent p)) ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1))))) :
    Nonempty (Module.Basis (ULift.{u} (Fin (n + 1))) Γ(U.toScheme, ⊤)
      Γ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.Omega p)), ⊤)) := by
  obtain ⟨eU⟩ := htriv
  -- Step 1: factor `s` through the open `Zx`.
  have hrange : Set.range s.base ⊆ Set.range Zx.ι.base := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    exact hsZx c
  obtain ⟨s', hfac⟩ : ∃ s' : C ⟶ Zx.toScheme, s' ≫ Zx.ι = s :=
    ⟨_, AlgebraicGeometry.IsOpenImmersion.lift_fac Zx.ι s hrange⟩
  let q : Zx.toScheme ⟶ C := Zx.ι ≫ p
  -- `Ω_{Z/C}|_{Zx} ≅ Ω_{Zx/C}` (Stacks 01US).
  have eΩ : (AlgebraicGeometry.Scheme.Modules.pullback Zx.ι).obj (AlgebraicGeometry.Omega p) ≅
      AlgebraicGeometry.Omega q :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback Zx.ι).symm.app _ ≪≫
      AlgebraicGeometry.Omega.restrictIso p q Zx.ι (𝟙 C) (Category.comp_id q)
  -- `T_{Z/C}|_{Zx} ≅ T_{Zx/C}`: dual commutes with open restriction.
  obtain ⟨eD⟩ := AlgebraicGeometry.Scheme.Modules.dual_restrict (AlgebraicGeometry.Omega p) Zx
  have eT : (AlgebraicGeometry.Scheme.Modules.pullback Zx.ι).obj
      (AlgebraicGeometry.relativeTangent p) ≅ AlgebraicGeometry.relativeTangent q :=
    eD ≪≫ AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso eΩ.symm
  let G : C.Modules := (AlgebraicGeometry.Scheme.Modules.pullback s').obj (AlgebraicGeometry.Omega q)
  let E : C.Modules :=
    (AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.relativeTangent p)
  have eE : E ≅ (AlgebraicGeometry.Scheme.Modules.pullback s').obj
      (AlgebraicGeometry.relativeTangent q) :=
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hfac.symm).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp s' Zx.ι).symm.app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback s').mapIso eT
  have eG : (AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.Omega p) ≅ G :=
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hfac.symm).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp s' Zx.ι).symm.app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback s').mapIso eΩ
  -- Step 2: `G` is locally free of finite type.
  have hsm : AlgebraicGeometry.Smooth q :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth (n + 1) q
  have hΩlf : (AlgebraicGeometry.Omega q).IsLocallyFree :=
    AlgebraicGeometry.isLocallyFree_omega_of_smooth q
  have hΩft : (AlgebraicGeometry.Omega q).IsFiniteType := AlgebraicGeometry.Omega_isFiniteType q
  have hGlf : G.IsLocallyFree :=
    (AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback s' (AlgebraicGeometry.Omega q)).1
  have hGft : G.IsFiniteType :=
    AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback s' (AlgebraicGeometry.Omega q)
  -- Step 3: `G^∨ ≅ E`, hence `s^*Ω ≅ G ≅ G^∨∨ ≅ E^∨`.
  obtain ⟨eDP⟩ := AlgebraicGeometry.Scheme.Modules.dual_pullback s' (AlgebraicGeometry.Omega q)
  have eDG : AlgebraicGeometry.Scheme.Modules.dual G ≅ E := eDP ≪≫ eE.symm
  obtain ⟨eDD⟩ := AlgebraicGeometry.Scheme.Modules.dual_dual G
  have e1 : (AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.Omega p) ≅
      AlgebraicGeometry.Scheme.Modules.dual E :=
    eG ≪≫ eDD.symm ≪≫ (AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso eDG).symm
  -- Step 4: restrict to `U`.
  let F : U.toScheme.Modules :=
    SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1)))
  obtain ⟨eR⟩ := AlgebraicGeometry.Scheme.Modules.dual_restrict E U
  obtain ⟨eF⟩ := AlgebraicGeometry.Scheme.Modules.dual_free_iso (X := U.toScheme) (n + 1)
  have e2 : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.Omega p)) ≅ F :=
    (AlgebraicGeometry.Scheme.Modules.pullback U.ι).mapIso e1 ≪≫ eR ≪≫
      AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso eU.symm ≪≫ eF
  -- Step 5: global sections.
  let e3 : Γ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.Omega p)), ⊤)
      ≃ₗ[Γ(U.toScheme, ⊤)] Γ(F, ⊤) :=
    ((SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤)).mapIso e2).toLinearEquiv
  let b0 : Module.Basis (Fin (n + 1)) Γ(U.toScheme, ⊤) Γ(F, ⊤) :=
    MiyaokaMori.ExteriorPowerFiniteFree.finiteFreeSectionBasis U.toScheme (n + 1) ⊤
  exact ⟨(b0.reindex Equiv.ulift.symm).map e3.symm⟩

end
