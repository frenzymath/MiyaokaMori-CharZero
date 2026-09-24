import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentHomGraph
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01lc
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupportBasics
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesQuasicoherentClosure
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FiniteTypeOfFiniteAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01pbAffineOpen

/-! # Extending a stalk map to a morphism of coherent sheaves, step 2: coherence and support of the graph

For `φ ∈ Hom_{O_V}(G|_V, F|_V)` on a locally Noetherian scheme `X`, the graph
`G' = ker (G ⊕ F → j_* j^* F)` of `…_StalkHomSpread_Graph.lean` is coherent when `G`, `F` are, and
`Supp G' ⊆ Supp G ∪ Supp F`.

* `j_* j^* F` is quasi-coherent: `j = V.ι` is quasi-compact (open immersion into a locally Noetherian
  scheme, Mathlib) and quasi-separated (a monomorphism), `j^* F` is quasi-coherent (Mathlib
  `isQuasicoherent_restrictFunctor`), so Stacks 01LC (`isQuasicoherent_pushforward`, `Stacks01lc.lean`)
  applies.
* `G ⊕ F` is coherent: quasi-coherent because `G ⊞ F ≅ ⨁ pairFunction G F` (Mathlib
  `biprod.uniqueUpToIso`) and finite biproducts of quasi-coherent modules are quasi-coherent
  (`isQuasicoherent_biproduct_of_fintype`); of finite type by the affine criterion
  `isFiniteType_of_finite_affine_sections`: over an affine `U`, `Γ(G ⊞ F, U)` embeds `Γ(X, U)`-linearly
  into `Γ(G, U) × Γ(F, U)` by `(pr₁, pr₂)` (`biprod.total` on sections), and both factors are finite
  modules (`finite_sections_of_isFiniteType`, Stacks 01PB).
* `G' = ker k` is quasi-coherent (Stacks 01IC, `isQuasicoherent_kernel`) and a subsheaf of the coherent
  `G ⊕ F`, hence coherent (Stacks 01Y1, `isCoherent_of_mono`).
* `Supp G' ⊆ Supp (G ⊕ F)` (`support_subset_of_mono`) and `Supp (G ⊕ F) ⊆ Supp G ∪ Supp F` (a point of
  the stalk of `G ⊕ F` is `inl a + inr b`, `map_total`, so the stalk vanishes where both stalks vanish).

Source: Stacks 01Y8 via the fibre product formulation; Stacks 01LC, 01IC, 01Y1. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.StalkHomSpread

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} (G F : X.Modules)

/-- `G ⊞ F ≅ ⨁ pairFunction G F`. -/
def biprodIsoBiproductPair : G ⊞ F ≅ ⨁ pairFunction G F :=
  (biprod.uniqueUpToIso G F
    ((biproduct.bicone (pairFunction G F)).toBinaryBiconeIsBilimit.symm
      (biproduct.isBilimit (pairFunction G F)))).symm

theorem isQuasicoherent_biprod [G.IsQuasicoherent] [F.IsQuasicoherent] :
    (G ⊞ F).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (biprodIsoBiproductPair G F).symm
    (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct_of_fintype (pairFunction G F)
      (fun j => by cases j <;> assumption))

/-- On sections, `s = inl (fst s) + inr (snd s)` (`biprod.total`). -/
theorem biprod_sections_total (U : X.Opens) (s : Γ(G ⊞ F, U)) :
    s = (biprod.inl : G ⟶ G ⊞ F).app U ((biprod.fst : G ⊞ F ⟶ G).app U s) +
      (biprod.inr : F ⟶ G ⊞ F).app U ((biprod.snd : G ⊞ F ⟶ F).app U s) := by
  have h := congrArg (fun ψ : (G ⊞ F ⟶ G ⊞ F) => ψ.app U s) (biprod.total (X := G) (Y := F))
  simp only [AlgebraicGeometry.Scheme.Modules.Hom.add_app, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.Hom.id_app] at h
  exact h.symm

variable [AlgebraicGeometry.IsLocallyNoetherian X]

/-- Over an affine open of a locally Noetherian scheme, the sections of `G ⊞ F` form a finite module
when those of `G`, `F` do. -/
theorem finite_sections_biprod [G.IsQuasicoherent] [F.IsQuasicoherent] [G.IsFiniteType]
    [F.IsFiniteType] {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(G ⊞ F, U) := by
  have hG : Module.Finite Γ(X, U) Γ(G, U) :=
    AlgebraicGeometry.Scheme.Modules.finite_sections_of_isFiniteType G hU
  have hF : Module.Finite Γ(X, U) Γ(F, U) :=
    AlgebraicGeometry.Scheme.Modules.finite_sections_of_isFiniteType F hU
  have hnoeth : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsNoetherian Γ(X, U) (Γ(G, U) × Γ(F, U)) := isNoetherian_of_isNoetherianRing_of_finite _ _
  let f : Γ(G ⊞ F, U) →ₗ[Γ(X, U)] Γ(G, U) × Γ(F, U) :=
    { toFun := fun s => ((biprod.fst : G ⊞ F ⟶ G).app U s, (biprod.snd : G ⊞ F ⟶ F).app U s)
      map_add' := fun a b => by
        ext <;> simp only [map_add, Prod.fst_add, Prod.snd_add]
      map_smul' := fun r m => by
        ext <;> simp only [AlgebraicGeometry.Scheme.Modules.Hom.app_smul, Prod.smul_fst,
          Prod.smul_snd, RingHom.id_apply] }
  refine Module.Finite.of_injective f fun a b hab => ?_
  have h1 : (biprod.fst : G ⊞ F ⟶ G).app U a = (biprod.fst : G ⊞ F ⟶ G).app U b :=
    congrArg Prod.fst hab
  have h2 : (biprod.snd : G ⊞ F ⟶ F).app U a = (biprod.snd : G ⊞ F ⟶ F).app U b :=
    congrArg Prod.snd hab
  rw [biprod_sections_total G F U a, biprod_sections_total G F U b, h1, h2]

theorem isCoherent_biprod [hG : G.IsCoherent] [hF : F.IsCoherent] : (G ⊞ F).IsCoherent := by
  have := hG.quasicoherent
  have := hF.quasicoherent
  have := hG.finiteType
  have := hF.finiteType
  have h2 : (G ⊞ F).IsQuasicoherent := isQuasicoherent_biprod G F
  refine ⟨h2, AlgebraicGeometry.Scheme.Modules.isFiniteType_of_finite_affine_sections (G ⊞ F)
    fun x => ?_⟩
  obtain ⟨⟨U, hU⟩, hxU⟩ : ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
    have : x ∈ (⊤ : X.Opens) := trivial
    rw [← AlgebraicGeometry.iSup_affineOpens_eq_top X] at this
    exact Opens.mem_iSup.mp this
  exact ⟨U, hU, hxU, finite_sections_biprod G F hU⟩

variable {V : X.Opens}

theorem isQuasicoherent_pushRestrict [F.IsQuasicoherent] :
    (pushRestrict F (V := V)).IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward V.ι (F.restrict V.ι)

variable (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule G F V)

/-- The graph `G' = ker (G ⊕ F → j_* j^* F)` is coherent (Stacks 01LC + 01IC + 01Y1). -/
theorem graph_isCoherent [hG : G.IsCoherent] [hF : F.IsCoherent] : (graph G F φ).IsCoherent := by
  have := hG.quasicoherent
  have := hF.quasicoherent
  have h1 : (G ⊞ F).IsQuasicoherent := isQuasicoherent_biprod G F
  have h2 : (pushRestrict F (V := V)).IsQuasicoherent := isQuasicoherent_pushRestrict F
  have h3 : (graph G F φ).IsQuasicoherent :=
    (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel (kmap G F φ)).1
  have h4 : (G ⊞ F).IsCoherent := isCoherent_biprod G F
  exact AlgebraicGeometry.Scheme.Modules.isCoherent_of_mono (kernel.ι (kmap G F φ))

omit [AlgebraicGeometry.IsLocallyNoetherian X] in
theorem support_biprod_subset : (G ⊞ F).support ⊆ G.support ∪ F.support := by
  intro x hx
  by_contra h
  rw [Set.mem_union, not_or] at h
  have h1 : Subsingleton ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj G) :=
    not_nontrivial_iff_subsingleton.mp
      (fun hn => h.1 ((AlgebraicGeometry.Scheme.Modules.mem_support_iff G x).mpr hn))
  have h2 : Subsingleton ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj F) :=
    not_nontrivial_iff_subsingleton.mp
      (fun hn => h.2 ((AlgebraicGeometry.Scheme.Modules.mem_support_iff F x).mpr hn))
  have h3 : Subsingleton ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj (G ⊞ F)) := by
    constructor
    intro p q
    rw [← map_total G F x p, ← map_total G F x q,
      Subsingleton.elim (((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map biprod.fst).hom p)
        (((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map biprod.fst).hom q),
      Subsingleton.elim (((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map biprod.snd).hom p)
        (((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map biprod.snd).hom q)]
  exact not_nontrivial_iff_subsingleton.mpr h3
    ((AlgebraicGeometry.Scheme.Modules.mem_support_iff (G ⊞ F) x).mp hx)

omit [AlgebraicGeometry.IsLocallyNoetherian X] in
/-- `Supp G' ⊆ Supp G ∪ Supp F`. -/
theorem graph_support_subset : (graph G F φ).support ⊆ G.support ∪ F.support :=
  (AlgebraicGeometry.Scheme.Modules.support_subset_of_mono (kernel.ι (kmap G F φ))).trans
    (support_biprod_subset G F)

end MiyaokaMori.StalkHomSpread

end
