import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift

/-! # Epimorphisms of sheaves of modules are local on an open cover

A morphism of `O_X`-modules whose restriction to each member of an open cover is an epimorphism is an
epimorphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.Modules.epi_of_openCover {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (φ : M ⟶ N) (𝒰 : X.OpenCover)
    (h : ∀ i, CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map φ)) :
    CategoryTheory.Epi φ := by
  rw [AlgebraicGeometry.Scheme.Modules.epi_iff_locally_surjective_sections]
  intro U s p hp
  obtain ⟨y, hy⟩ := 𝒰.covers p
  let i := 𝒰.idx p
  let f := 𝒰.f i
  have hyf : f y = p := hy
  let Upre : (𝒰.X i).Opens := f ⁻¹ᵁ U
  have hyUpre : y ∈ Upre := by
    change f y ∈ U
    exact hyf ▸ hp
  let Vbase : X.Opens := f ''ᵁ Upre
  have hVbase : Vbase ≤ U := f.image_preimage_le U
  let rM := M.restrict f
  let rN := N.restrict f
  let ψ : rM ⟶ rN := (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map φ
  have hψ : CategoryTheory.Epi ψ := by
    have he := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback f
    have hn := he.hom.naturality φ
    have hleft : CategoryTheory.Epi (he.hom.app M ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map φ) := by
      infer_instance
    have hright : CategoryTheory.Epi (ψ ≫ he.hom.app N) := by
      rw [hn]
      exact hleft
    exact (CategoryTheory.epi_comp_iff_of_isIso ψ (he.hom.app N)).mp hright
  let sbase : Γ(N, Vbase) := N.presheaf.map (homOfLE hVbase).op s
  let sR : Γ(rN, Upre) := (N.restrictAppIso f Upre).inv sbase
  obtain ⟨W, hWU, hyW, t, ht⟩ :=
    (AlgebraicGeometry.Scheme.Modules.epi_iff_locally_surjective_sections ψ).mp hψ
      Upre sR y hyUpre
  let V : X.Opens := f ''ᵁ W
  have hpV : p ∈ V := by
    exact ⟨y, hyW, hyf⟩
  have hVU : V ≤ U := (f.image_mono hWU).trans hVbase
  let yX : Γ(M, V) := (M.restrictAppIso f W).hom t
  refine ⟨V, hVU, hpV, yX, ?_⟩
  have ht' := congrArg (fun z => (N.restrictAppIso f W).hom z) ht
  dsimp [yX, V, ψ, rM, rN, sR, sbase, Vbase] at ht' ⊢
  have hleft :
      (N.restrictAppIso f W).hom ((AlgebraicGeometry.Scheme.Modules.Hom.app
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map φ) W) t) =
        (AlgebraicGeometry.Scheme.Modules.Hom.app φ (f ''ᵁ W))
          ((M.restrictAppIso f W).hom t) := by
    rfl
  rw [← hleft, ht]
  have hmap := AlgebraicGeometry.Scheme.Modules.map_restrictAppIso_hom f N
    (U := W) (V := Upre) (homOfLE hWU).op
  rw [← ConcreteCategory.comp_apply]
  rw [hmap]
  rw [ConcreteCategory.comp_apply]
  simp [sR, sbase]
  let hVW : V ≤ Vbase := f.image_mono hWU
  change N.presheaf.map (homOfLE hVW).op
      (N.presheaf.map (homOfLE hVbase).op s) =
    N.presheaf.map (homOfLE hVU).op s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 1

end
