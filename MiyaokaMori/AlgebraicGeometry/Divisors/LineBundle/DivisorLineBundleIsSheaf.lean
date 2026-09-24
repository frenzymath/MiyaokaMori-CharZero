import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleSections
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.PresheafOfModulesSheafSections

/-! # The subpresheaf `O_X(D)` of `𝒦_X` is a sheaf

The subpresheaf `CartierDivisor.lineBundlePresheaf D` of `𝒦_X` (defined by the local condition
`h·g ∈ O_X`) is already a sheaf; hence the sections of its sheafification `CartierDivisor.lineBundleModules D`
over an open `W` are `CartierDivisor.lineBundleSections D W`, and the linear isomorphism
`CartierDivisor.lineBundleSectionEquiv` commutes with restriction.

Proof:
1. Use the unique-gluing form of the sheaf condition (`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`);
   `𝒦_X` is a sheaf, so compatible families glue uniquely in `𝒦_X`.
2. The membership condition is pointwise local: the glued section agrees near every point with some
   `sf_i`, and the witness of `sf_i` at that point still works.
3. The section isomorphism comes from the sections of the sheafification of a presheaf of modules that
   is already a sheaf.
Source: Hartshorne II.6.13 (`L(D)` as a subsheaf of `𝒦`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The subpresheaf `O_X(D)` of `𝒦_X` is a sheaf. -/
theorem CartierDivisor.lineBundlePresheaf_isSheaf {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X.toScheme)
      (CartierDivisor.lineBundlePresheaf D).presheaf := by
  change TopCat.Presheaf.IsSheaf _
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  let K := X.toScheme.rationalFunctionsSheaf
  let sf' : ∀ i, K.val.obj (op (U i)) := fun i => (sf i).1
  have hsf' : TopCat.Presheaf.IsCompatible K.val U sf' := fun i j => congrArg Subtype.val (hsf i j)
  obtain ⟨h, hh, huniq⟩ := K.existsUnique_gluing U sf' hsf'
  have hmem : h ∈ CartierDivisor.lineBundleSections D (iSup U) := by
    intro x hx
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨W, hxW, hWU, g, hg, hprod⟩ := (sf i).2 x hxi
    refine ⟨W, hxW, hWU.trans (le_iSup U i), g, hg, ?_⟩
    have heq : K.val.map (homOfLE (hWU.trans (le_iSup U i))).op =
        K.val.map (Opens.leSupr U i).op ≫ K.val.map (homOfLE hWU).op := by
      rw [← Functor.map_comp]; rfl
    have hK : (K.val.map (homOfLE (hWU.trans (le_iSup U i))).op).hom h =
        (K.val.map (homOfLE hWU).op).hom (sf i).1 :=
      (congrArg (fun q => q.hom h) heq).trans
        (congrArg (K.val.map (homOfLE hWU).op).hom (hh i))
    rw [hK]
    exact hprod
  refine ⟨⟨h, hmem⟩, fun i => Subtype.ext (hh i), fun s hs => Subtype.ext ?_⟩
  exact huniq s.1 (fun i => congrArg Subtype.val (hs i))

/-- `Γ(O_X(D), W)` is the submodule `lineBundleSections D W` of `𝒦_X(W)`. -/
def CartierDivisor.lineBundleSectionEquiv {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) (W : X.toScheme.Opens) :
    CartierDivisor.lineBundleSections D W ≃ₗ[Γ(X.toScheme, W)]
      Γ(CartierDivisor.lineBundleModules D, W) :=
  MiyaokaMori.PresheafOfModulesSheafSections.sectionEquiv
    (CartierDivisor.lineBundlePresheaf D) (CartierDivisor.lineBundlePresheaf_isSheaf D) W

/-- The section isomorphism commutes with restriction. -/
theorem CartierDivisor.lineBundleSectionEquiv_restrict {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) {W W' : X.toScheme.Opens} (hW : W' ≤ W)
    (h : CartierDivisor.lineBundleSections D W) :
    (CartierDivisor.lineBundleModules D).presheaf.map (homOfLE hW).op
        (CartierDivisor.lineBundleSectionEquiv D W h) =
      CartierDivisor.lineBundleSectionEquiv D W'
        (CartierDivisor.lineBundleRestrict D (homOfLE hW) h) :=
  MiyaokaMori.PresheafOfModulesSheafSections.sectionEquiv_restrict
    (CartierDivisor.lineBundlePresheaf D) (CartierDivisor.lineBundlePresheaf_isSheaf D)
    (homOfLE hW) h

end
