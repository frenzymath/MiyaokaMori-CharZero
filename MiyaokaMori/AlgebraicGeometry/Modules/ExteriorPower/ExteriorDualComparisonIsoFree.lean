import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualSheafComparison
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualComparisonIsoExt
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualComparisonIsoBasis
import MiyaokaMori.Algebra.ExteriorPowerDualPairing
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrame
import MiyaokaMori.Algebra.ExteriorPowerBijectiveHelpers
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv

/-!
# The exterior-dual comparison is invertible for a module sheaf with compatible section bases

Let `G : X.Modules` carry a finite frame on `⊤`, `he : IsFrameOn G e` with `e : I → Γ(G, ⊤)`, `I` finite
(`MiyaokaMori.DualPullback.IsFrameOn`; it gives a basis `he.basisOn V` of `Γ(G, V)` over `Γ(X, V)` for every
open `V`, compatible with restriction; e.g. the free sheaf of rank `r` with its standard basis,
`freeIsFrameOn`). Then `exteriorDualComparison G n : ⋀ⁿ(G^∨) ⟶ (⋀ⁿ G)^∨` is an isomorphism for every `n`
(`exteriorDualComparison_isIso_of_isFrameOn`), hence so is the comparison of the free sheaf
(`exteriorDualComparison_free_isIso`).

The statement is for `IsFrameOn` (`exteriorDualComparison_isIso_of_isFrameOn`); the index type is any
finite `I : Type u`, and the pairing lemma is applied to the basis reindexed along `Fintype.equivFin I`.

Proof. Invertibility is checked on sections over each open `U` (`isIso_of_bijective`). Over `U`
there is a commutative square (`topPairing_comparison`)

`topPairing ∘ (edc G n).app U ∘ unit = pairingDual ∘ ⋀ⁿ(evalTop ∘ sectionEquiv⁻¹)`

where `unit : ⋀ⁿ Γ(G^∨, U) → Γ(⋀ⁿ(G^∨), U)` is the sheafification unit,
`evalTop ∘ sectionEquiv⁻¹ : Γ(G^∨, U) ≃ Module.Dual Γ(G, U)` reads a dual section as its top-level
functional (bijective because of the compatible bases, `FrameDual.evalTopEquiv he`),
`pairingDual : ⋀ⁿ(Γ(G,U)^∨) → (⋀ⁿ Γ(G,U))^∨` is Mathlib's pairing (bijective for a free module,
`exteriorPowerPairingDual_bijective`), and `topPairing` reads a section of `(⋀ⁿ G)^∨` as the
functional on `⋀ⁿ Γ(G, U)` obtained from its top-level functional through the unit. Both sides of
the square are the determinant of functional values on wedges (`exteriorDualComparison_wedge_eval`,
`pairingDual_ιMulti_ιMulti`).
* Injectivity: a section `s` of `⋀ⁿ(G^∨)` is locally a unit image (`moduleExteriorPower_imageSieve_mem`);
  if `edc s = 0` the square kills the local preimages, so `s` vanishes locally, hence globally
  (the exterior power is a sheaf, `Presheaf.IsSheaf.isSeparated`).
* Surjectivity: given `σ`, the right-hand side of the square is surjective, giving `p` with
  `edc (unit p)` and `σ` having the same top-level functional on `⋀ⁿ Γ(G, U)`. Two compatible
  families of functionals on `⋀ⁿ G` over `U` agreeing on wedges over `U` agree on wedges over
  every `V ≤ U` (multilinearity, `Module.Basis.ext_multilinear` with the basis over `V`, whose
  vectors are restrictions of the basis over `U`, and compatibility with restriction), hence agree
  (`localDual_ext_of_wedge`).

Sources: Stacks Project, `modules.tex`, Symmetric and exterior powers (`lemma-local-tensor-algebra`)
and Internal Hom; Mathlib's exterior-power pairing and basis; `exteriorPower_map_bijective` from
`ExteriorPowerBijectiveHelpers`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules
open MiyaokaMori.Algebra

universe u

set_option backward.isDefEq.respectTransparency false

open ModuleDualSheafificationUnit MiyaokaMori.DualPullback
open MiyaokaMori.ModuleDualSectionEquiv (unit_isIso unitIso unitIso_hom sectionEquiv sectionEquiv_apply
  sectionEquiv_restrict)

namespace ExteriorDualComparisonFree

variable {X : Scheme.{u}} {G : X.Modules} {I : Type u} [Fintype I] {e : I → Γ(G, ⊤)}
  (he : IsFrameOn G e) (n : ℕ)

local instance exteriorDualComparisonFreeSectionCommRing (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- A dual section over `U` read as a functional on `Γ(G, U)`. -/
def dualSectionsToDual (U : X.Opens) :
    Γ(moduleSheafDual G, U) ≃ₗ[Γ(X, U)] Module.Dual Γ(X, U) Γ(G, U) :=
  (sectionEquiv G U).symm ≪≫ₗ FrameDual.evalTopEquiv he U

theorem dualSectionsToDual_apply (U : X.Opens) (s : Γ(moduleSheafDual G, U)) (t : Γ(G, U)) :
    dualSectionsToDual he U s t = ((sectionEquiv G U).symm s).1 (Over.mk (𝟙 U)) t := rfl

/-- The sheafification unit of the exterior presheaf of `M` over `U`, as a linear map. -/
def unitLinear (M : X.Modules) (U : X.Opens) :
    ⋀[Γ(X, U)]^n Γ(M, U) →ₗ[Γ(X, U)] Γ(moduleExteriorPower X M n, U) :=
  ((moduleExteriorSheafUnit X M n).app (op U)).hom

theorem unitLinear_ιMulti (M : X.Modules) (U : X.Opens) (v : Fin n → Γ(M, U)) :
    unitLinear n M U (exteriorPower.ιMulti Γ(X, U) n v) = moduleExteriorWedge X M n U v := rfl

/-- The comparison on sections over `U`, as a linear map. -/
def comparisonLinear (U : X.Opens) :
    Γ(moduleExteriorPower X (moduleSheafDual G) n, U) →ₗ[Γ(X, U)]
      Γ(moduleSheafDual (moduleExteriorPower X G n), U) :=
  ((exteriorDualComparison G n).val.app (op U)).hom

theorem comparisonLinear_apply (U : X.Opens) (s : Γ(moduleExteriorPower X (moduleSheafDual G) n, U)) :
    comparisonLinear n U s = (exteriorDualComparison G n).app U s := rfl

/-- A section of `(⋀ⁿ G)^∨` over `U` read as a functional on `⋀ⁿ Γ(G, U)`. -/
def topPairing (U : X.Opens) :
    Γ(moduleSheafDual (moduleExteriorPower X G n), U) →ₗ[Γ(X, U)]
      Module.Dual Γ(X, U) (⋀[Γ(X, U)]^n Γ(G, U)) :=
  LinearMap.lcomp Γ(X, U) Γ(X, U) (unitLinear n G U) ∘ₗ
    (FrameDual.evalTop U) ∘ₗ (sectionEquiv (moduleExteriorPower X G n) U).symm.toLinearMap

theorem topPairing_apply (U : X.Opens) (σ : Γ(moduleSheafDual (moduleExteriorPower X G n), U))
    (p : ⋀[Γ(X, U)]^n Γ(G, U)) :
    topPairing n U σ p =
      ((sectionEquiv (moduleExteriorPower X G n) U).symm σ).1 (Over.mk (𝟙 U))
        (unitLinear n G U p) := rfl

/-- The square: the comparison, read on top-level functionals, is Mathlib's pairing. -/
theorem topPairing_comparison (U : X.Opens) (p : ⋀[Γ(X, U)]^n Γ(moduleSheafDual G, U)) :
    topPairing n U ((exteriorDualComparison G n).app U (unitLinear n (moduleSheafDual G) U p)) =
      exteriorPower.pairingDual Γ(X, U) Γ(G, U) n
        (exteriorPower.map n (dualSectionsToDual he U).toLinearMap p) := by
  have hlin : (topPairing n U ∘ₗ comparisonLinear n U ∘ₗ unitLinear n (moduleSheafDual G) U) =
      exteriorPower.pairingDual Γ(X, U) Γ(G, U) n ∘ₗ
        exteriorPower.map n (dualSectionsToDual he U).toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro Φ
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change topPairing n U (comparisonLinear n U
        (unitLinear n (moduleSheafDual G) U (exteriorPower.ιMulti Γ(X, U) n Φ)))
        (exteriorPower.ιMulti Γ(X, U) n v) =
      exteriorPower.pairingDual Γ(X, U) Γ(G, U) n
        (exteriorPower.map n (dualSectionsToDual he U).toLinearMap
          (exteriorPower.ιMulti Γ(X, U) n Φ)) (exteriorPower.ιMulti Γ(X, U) n v)
    rw [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti, topPairing_apply,
      unitLinear_ιMulti, unitLinear_ιMulti, comparisonLinear_apply]
    exact exteriorDualComparison_wedge_eval G n U Φ (Over.mk (𝟙 U)) v
  exact LinearMap.congr_fun hlin p

include he in
/-- Injectivity of the comparison on sections over `U`. -/
theorem comparison_app_injective (U : X.Opens) :
    Function.Injective ((exteriorDualComparison G n).app U) := by
  intro s s' hss'
  -- reduce to `s - s' = 0`: work with `d := s - s'`
  suffices key : ∀ d : Γ(moduleExteriorPower X (moduleSheafDual G) n, U),
      (exteriorDualComparison G n).app U d = 0 → d = 0 by
    have := key (s - s') (by rw [map_sub, hss', sub_self])
    exact sub_eq_zero.mp this
  intro d hd
  have hsep := Presheaf.IsSheaf.isSeparated (J := Opens.grothendieckTopology X)
    (moduleExteriorPower X (moduleSheafDual G) n).isSheaf
  apply hsep U _ (moduleExteriorPower_imageSieve_mem (moduleSheafDual G) n U d) d 0
  intro V f hf
  obtain ⟨p, hp⟩ := hf
  change (moduleExteriorPower X (moduleSheafDual G) n).presheaf.map f.op d =
    (moduleExteriorPower X (moduleSheafDual G) n).presheaf.map f.op 0
  rw [map_zero]
  have hp' : (moduleExteriorPower X (moduleSheafDual G) n).presheaf.map f.op d =
      unitLinear n (moduleSheafDual G) V p := hp.symm
  rw [hp']
  -- the comparison kills `unit p`
  have h0 : (exteriorDualComparison G n).app V (unitLinear n (moduleSheafDual G) V p) = 0 := by
    rw [← hp']
    have hnat : (exteriorDualComparison G n).app V
        ((moduleExteriorPower X (moduleSheafDual G) n).presheaf.map f.op d) =
        (moduleSheafDual (moduleExteriorPower X G n)).presheaf.map f.op
          ((exteriorDualComparison G n).app U d) :=
      PresheafOfModules.naturality_apply (exteriorDualComparison G n).val f.op d
    rw [hnat, hd, map_zero]
  have h1 := topPairing_comparison he n V p
  rw [h0, map_zero] at h1
  have h2 : exteriorPower.map n (dualSectionsToDual he V).toLinearMap p = 0 :=
    (exteriorPowerPairingDual_bijective ((he.basisOn V).reindex (Fintype.equivFin I)) n).injective
      (h1.symm.trans (map_zero _).symm)
  have h3 : p = 0 :=
    (exteriorPower_map_bijective n (dualSectionsToDual he V).toLinearMap
      (dualSectionsToDual he V).bijective).injective
      (h2.trans (map_zero _).symm)
  rw [h3, map_zero]

include he in
/-- Two compatible families of functionals on `⋀ⁿ G` over `U` agreeing on wedges over `U` agree. -/
theorem localDual_ext_of_top (U : X.Opens)
    (ψ ψ' : LocalDualSections X (moduleExteriorPower X G n) U)
    (h : ∀ v : Fin n → Γ(G, U), ψ.1 (Over.mk (𝟙 U)) (moduleExteriorWedge X G n U v) =
      ψ'.1 (Over.mk (𝟙 U)) (moduleExteriorWedge X G n U v)) : ψ = ψ' := by
  apply localDual_ext_of_wedge
  intro V w
  -- both sides are multilinear in `w`; compare on basis tuples
  let m : MultilinearMap Γ(X, V.left) (fun _ : Fin n ↦ Γ(G, V.left)) Γ(X, V.left) :=
    (ψ.1 V).compMultilinearMap (moduleExteriorWedge X G n V.left).toMultilinearMap
  let m' : MultilinearMap Γ(X, V.left) (fun _ : Fin n ↦ Γ(G, V.left)) Γ(X, V.left) :=
    (ψ'.1 V).compMultilinearMap (moduleExteriorWedge X G n V.left).toMultilinearMap
  have hc : ∀ (χ : LocalDualSections X (moduleExteriorPower X G n) U)
      (x : Γ(moduleExteriorPower X G n, U)),
      χ.1 V ((moduleExteriorPower X G n).presheaf.map V.hom.op x) =
        X.presheaf.map V.hom.op (χ.1 (Over.mk (𝟙 U)) x) :=
    fun χ x ↦ χ.2 V (Over.mk (𝟙 U)) (Over.homMk V.hom) x
  have hm : m = m' := by
    apply Module.Basis.ext_multilinear (fun _ ↦ he.basisOn V.left)
    intro j
    change ψ.1 V (moduleExteriorWedge X G n V.left (fun i ↦ he.basisOn V.left (j i))) =
      ψ'.1 V (moduleExteriorWedge X G n V.left (fun i ↦ he.basisOn V.left (j i)))
    have hb : (fun i ↦ he.basisOn V.left (j i)) =
        G.presheaf.map V.hom.op ∘ (fun i ↦ he.basisOn U (j i)) := by
      funext i
      exact (he.basisOn_restrict V.hom (j i)).symm
    rw [hb, ← moduleExteriorWedge_restrict, hc ψ, hc ψ', h]
  exact congrArg
    (fun f : MultilinearMap Γ(X, V.left) (fun _ : Fin n ↦ Γ(G, V.left)) Γ(X, V.left) ↦ f w) hm

include he in
/-- Two sections of `(⋀ⁿ G)^∨` over `U` with the same functional on `⋀ⁿ Γ(G, U)` agree. -/
theorem localDual_ext_of_topPairing (U : X.Opens)
    (σ σ' : Γ(moduleSheafDual (moduleExteriorPower X G n), U))
    (h : topPairing n U σ = topPairing n U σ') : σ = σ' := by
  apply (sectionEquiv (moduleExteriorPower X G n) U).symm.injective
  apply localDual_ext_of_top he n U
  intro v
  have := LinearMap.congr_fun h (exteriorPower.ιMulti Γ(X, U) n v)
  rw [topPairing_apply, topPairing_apply, unitLinear_ιMulti] at this
  exact this

include he in
/-- Surjectivity of the comparison on sections over `U`. -/
theorem comparison_app_surjective (U : X.Opens) :
    Function.Surjective ((exteriorDualComparison G n).app U) := by
  intro σ
  obtain ⟨q, hq⟩ := (exteriorPowerPairingDual_bijective
    ((he.basisOn U).reindex (Fintype.equivFin I)) n).surjective
    (topPairing n U σ)
  obtain ⟨p, hp⟩ := (exteriorPower_map_bijective n (dualSectionsToDual he U).toLinearMap
    (dualSectionsToDual he U).bijective).surjective q
  refine ⟨unitLinear n (moduleSheafDual G) U p, ?_⟩
  apply localDual_ext_of_topPairing he n U
  rw [topPairing_comparison he n U p, hp, hq]

include he in
/-- Bijectivity of the comparison on sections over every open. -/
theorem comparison_app_bijective (U : X.Opens) :
    Function.Bijective ((exteriorDualComparison G n).app U) :=
  ⟨comparison_app_injective he n U, comparison_app_surjective he n U⟩

end ExteriorDualComparisonFree

/-- The exterior-dual comparison is invertible for a module sheaf with a finite frame on `⊤`, in
every exterior degree. -/
theorem exteriorDualComparison_isIso_of_isFrameOn {X : Scheme.{u}} {G : X.Modules} {I : Type u}
    [Fintype I] {e : I → Γ(G, ⊤)} (he : MiyaokaMori.DualPullback.IsFrameOn G e) (n : ℕ) :
    IsIso (exteriorDualComparison G n) :=
  Scheme.Modules.isIso_of_bijective _ fun U ↦
    ExteriorDualComparisonFree.comparison_app_bijective he n U

end AlgebraicGeometry.Scheme.Modules
