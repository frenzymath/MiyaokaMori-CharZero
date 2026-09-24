import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestriction
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSheafificationUnit
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Extensionality on wedge sections for the sheafified exterior power

Two facts about the sheafified exterior power `moduleExteriorPower X M n` that reduce
statements about arbitrary sections to statements about wedge sections:

* `moduleExteriorPower_hom_ext`: two module-sheaf morphisms out of `⋀ⁿ M` agree as soon as
  they agree on every wedge section over every open (the sheafification adjunction plus the
  universal property of the exterior power).
* `localDual_ext_of_wedge`: two compatible families of local functionals on `⋀ⁿ M` over `U`
  (elements of `LocalDualSections X (moduleExteriorPower X M n) U`) agree as soon as they agree
  on every wedge section over every open inside `U`. Proof: every section of the sheafification
  is locally in the image of the sheafification unit (Mathlib,
  `Presheaf.isLocallySurjective_toSheafify'`), the unit images are spanned by the wedges
  (`exteriorPower.linearMap_ext`), the families are compatible with restriction, and the
  structure sheaf is separated (`Presheaf.IsSheaf.isSeparated`).

Both are used by `ExteriorDualComparisonIsoRestrict` and `ExteriorDualComparisonIsoFree`.
Source: Stacks Project `sheaves.tex`, sheafification is locally surjective
(`lemma-sheafification-surjective`), and `modules.tex`, exterior powers.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (M : X.Modules) (n : ℕ)

local instance exteriorDualComparisonIsoExtSectionCommRing (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- Two morphisms out of the sheafified exterior power agree if they agree on all wedge
sections over all opens. -/
theorem moduleExteriorPower_hom_ext {K : X.Modules}
    {f g : moduleExteriorPower X M n ⟶ K}
    (h : ∀ (U : X.Opens) (v : Fin n → Γ(M, U)),
      f.app U (moduleExteriorWedge X M n U v) = g.app U (moduleExteriorWedge X M n U v)) :
    f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (moduleExteriorPresheaf X M.val n) K).injective
  rw [(PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit,
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  exact h U.unop v

/-- The sheafification unit of the exterior presheaf is locally surjective. -/
theorem moduleExteriorSheafUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (moduleExteriorSheafUnit X M n)) := by
  unfold moduleExteriorSheafUnit
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact Presheaf.isLocallySurjective_toSheafify' (Opens.grothendieckTopology X) _

/-- Every section of the sheafified exterior power is, on a covering sieve, the unit image of an
element of the exterior presheaf. -/
theorem moduleExteriorPower_imageSieve_mem (U : X.Opens)
    (t : Γ(moduleExteriorPower X M n, U)) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map (moduleExteriorSheafUnit X M n))
      (U := U) t ∈ Opens.grothendieckTopology X U :=
  haveI := moduleExteriorSheafUnit_isLocallySurjective M n
  Presheaf.imageSieve_mem (Opens.grothendieckTopology X) _ (U := op U) t

/-- Two compatible families of local functionals on the sheafified exterior power agree if
they agree on all wedge sections over all opens inside `U`. -/
theorem localDual_ext_of_wedge {U : X.Opens}
    (φ ψ : LocalDualSections X (moduleExteriorPower X M n) U)
    (h : ∀ (V : Over U) (v : Fin n → Γ(M, V.left)),
      φ.1 V (moduleExteriorWedge X M n V.left v) = ψ.1 V (moduleExteriorWedge X M n V.left v)) :
    φ = ψ := by
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro t
  -- unit images: the two functionals agree on the whole image of the unit over every open
  have hunit : ∀ (W : Over U) (p : (moduleExteriorPresheaf X M.val n).obj (op W.left)),
      φ.1 W ((moduleExteriorSheafUnit X M n).app (op W.left) p) =
        ψ.1 W ((moduleExteriorSheafUnit X M n).app (op W.left) p) := by
    intro W
    let u : ⋀[Γ(X, W.left)]^n Γ(M, W.left) →ₗ[Γ(X, W.left)]
        Γ(moduleExteriorPower X M n, W.left) :=
      ((moduleExteriorSheafUnit X M n).app (op W.left)).hom
    have hlin : (φ.1 W).comp u = (ψ.1 W).comp u := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      exact h W v
    intro p
    exact LinearMap.congr_fun hlin p
  -- separatedness of the structure sheaf along the image sieve of `t`
  have hsep := Presheaf.IsSheaf.isSeparated (J := Opens.grothendieckTopology X) X.sheaf.2
  apply hsep V.left _ (moduleExteriorPower_imageSieve_mem M n V.left t)
  intro W f hf
  obtain ⟨p, hp⟩ := hf
  let W' : Over U := Over.mk (f ≫ V.hom)
  have hφ : X.presheaf.map f.op (φ.1 V t) =
      φ.1 W' ((moduleExteriorPower X M n).presheaf.map f.op t) :=
    (φ.2 W' V (Over.homMk f) t).symm
  have hψ : X.presheaf.map f.op (ψ.1 V t) =
      ψ.1 W' ((moduleExteriorPower X M n).presheaf.map f.op t) :=
    (ψ.2 W' V (Over.homMk f) t).symm
  change X.presheaf.map f.op (φ.1 V t) = X.presheaf.map f.op (ψ.1 V t)
  rw [hφ, hψ]
  have hp' : (moduleExteriorPower X M n).presheaf.map f.op t =
      (moduleExteriorSheafUnit X M n).app (op W) p := hp.symm
  rw [hp']
  exact hunit W' p

end AlgebraicGeometry.Scheme.Modules
