import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualRestrictOpen
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerTopLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeTangentLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackRank
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01b6
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaOpenImmersionSquare
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor

/-! # Local frames of the cone tangent bundle

If the image of the section `s : C → Z` lies in an open subscheme that is smooth of relative dimension
`n+1` over `C`, then `s^*T_{Z/C}` has an affine frame near every point of `C`, indexed by
`ULift (Fin (n+1))` (§2.2 of the paper; Stacks 01V4, 01US).

Proof:
1. Factor `s` through the open subscheme `Zx` containing its image (`IsOpenImmersion.lift`,
   `s' ≫ Zx.ι = s`), and identify the restriction of `Ω_{Z/C}` to this open with `Ω_{Zx/C}` by
   `Omega.restrictIso` (Stacks 01US, with base direction `𝟙 C`); the dual commutes with open
   restriction (`dual_restrict`), so `T_{Z/C}|_{Zx} ≅ T_{Zx/C}`.
2. Smoothness of relative dimension `n+1` gives that `Ω_{Zx/C}` is locally free of finite type with
   pointwise rank `n+1`; the dual has the same rank (`isLocallyFree_relativeTangent`, `isFiniteType_dual`).
3. Pullback along the section preserves local freeness, finite type and rank (`isLocallyFree_pullback`,
   `isFiniteType_pullback`), and `pullbackComp`/`pullbackCongr` give
   `coneTangentBundle p s hs ≅ s'^* T_{Zx/C}`, so `coneTangentBundle` is locally free of finite type
   and rank `n+1`.
4. Use `exists_restrict_iso_free_fin` to get an open frame at each point, then shrink to an affine
   basic open containing the point by `isBasis_affineOpens` (`pullback_iso_free_of_le`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem coneTangentBundle_exists_affine_frame
    {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    {Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C.toScheme) (s : C.toScheme ⟶ Z)
    (hs : s ≫ p = CategoryTheory.CategoryStruct.id C.toScheme)
    (Zx : Z.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ p)]
    (x : C.toScheme) :
    ∃ U : C.toScheme.affineOpens, x ∈ U.1 ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj
          (coneTangentBundle p s hs) ≅
        SheafOfModules.free (R := U.1.toScheme.ringCatSheaf)
          (ULift.{u} (Fin (n + 1)))) := by
  -- Step 1: factor `s` through the open `Zx`.
  have hrange : Set.range s.base ⊆ Set.range Zx.ι.base := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    exact hsZx c
  obtain ⟨s', hfac⟩ : ∃ s' : C.toScheme ⟶ Zx.toScheme, s' ≫ Zx.ι = s :=
    ⟨_, AlgebraicGeometry.IsOpenImmersion.lift_fac Zx.ι s hrange⟩
  let q : Zx.toScheme ⟶ C.toScheme := Zx.ι ≫ p
  -- `Ω_{Z/C}|_{Zx} ≅ Ω_{Zx/C}` (Stacks 01US).
  have eΩ : (AlgebraicGeometry.Scheme.Modules.pullback Zx.ι).obj (AlgebraicGeometry.Omega p) ≅
      AlgebraicGeometry.Omega q :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback Zx.ι).symm.app _ ≪≫
      AlgebraicGeometry.Omega.restrictIso p q Zx.ι (𝟙 C.toScheme) (Category.comp_id q)
  -- `T_{Z/C}|_{Zx} ≅ T_{Zx/C}`: dual commutes with open restriction.
  obtain ⟨eD⟩ := AlgebraicGeometry.Scheme.Modules.dual_restrict (AlgebraicGeometry.Omega p) Zx
  have eT : (AlgebraicGeometry.Scheme.Modules.pullback Zx.ι).obj (AlgebraicGeometry.relativeTangent p) ≅
      AlgebraicGeometry.relativeTangent q :=
    eD ≪≫ AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso eΩ.symm
  -- `E = s^* T_{Z/C} ≅ s'^* T_{Zx/C}`.
  let F : C.toScheme.Modules :=
    (AlgebraicGeometry.Scheme.Modules.pullback s').obj (AlgebraicGeometry.relativeTangent q)
  have eE : coneTangentBundle p s hs ≅ F :=
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hfac.symm).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp s' Zx.ι).symm.app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback s').mapIso eT
  -- Step 2: `T_{Zx/C}` is locally free, finite type, of rank `n+1`.
  have hsm : AlgebraicGeometry.Smooth q :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth (n + 1) q
  obtain ⟨hTlf, hTrk⟩ := AlgebraicGeometry.isLocallyFree_relativeTangent (n + 1) q
  have hΩft : (AlgebraicGeometry.Omega q).IsFiniteType := AlgebraicGeometry.Omega_isFiniteType q
  have hΩlf : (AlgebraicGeometry.Omega q).IsLocallyFree :=
    AlgebraicGeometry.isLocallyFree_omega_of_smooth q
  have hTft : (AlgebraicGeometry.relativeTangent q).IsFiniteType :=
    AlgebraicGeometry.Scheme.Modules.isFiniteType_dual (AlgebraicGeometry.Omega q) hΩlf
  -- Step 3: pullback along `s'` preserves these.
  have hF := AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback s'
    (AlgebraicGeometry.relativeTangent q)
  have hFlf : F.IsLocallyFree := hF.1
  have hFft : F.IsFiniteType :=
    AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback s' (AlgebraicGeometry.relativeTangent q)
  have hFrk : ∀ c : C.toScheme, AlgebraicGeometry.Scheme.Modules.rankAtStalk F c = n + 1 :=
    fun c => (hF.2 c).trans (hTrk _)
  -- Step 4: a frame near `x`, shrunk to an affine open.
  obtain ⟨U, hxU, ⟨eU⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_restrict_iso_free_fin F (n + 1) hFrk x
  obtain ⟨V, hV, hxV, hVU⟩ :=
    (Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens C.toScheme)) hxU
  obtain ⟨eV⟩ := AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le F hVU
    (ULift.{u} (Fin (n + 1)))
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app F ≪≫ eU)
  refine ⟨⟨V, hV⟩, hxV, ⟨?_⟩⟩
  exact (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.Opens.ι V)).mapIso eE ≪≫ eV

end
