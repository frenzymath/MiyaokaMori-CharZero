import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber

/-! # Vanishing at a point is invariant under isomorphisms

Vanishing of a global section at a point is invariant under an isomorphism of sheaves
of modules: for `θ : M ≅ M'` and `s ∈ Γ(X, M)`, `IsZeroAt (θ s) x ↔ IsZeroAt s x`.

This is immediate from the definition of `IsZeroAt` (the germ `s_x ∈ M_x` lies in `𝔪_x • M_x`).
It is used to transport the nowhere-vanishing hypothesis of `projectivizationMorphism` along an
isomorphism of line bundles.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

/-- Step 3 of the proof below, for any morphism `φ : M ⟶ M'` of sheaves of modules: the stalk map
`AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x φ` is `O_{X,x}`-linear and compatible with germs
(`AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ`), so it carries `𝔪_x • M_x` into `𝔪_x • M'_x`. Hence
`IsZeroAt s x → IsZeroAt (φ s) x`. (Same argument as `isZeroAt_map` in
`SeedSectionInPunctured`, restated here with `Hom.app` so that this
module stays light.) -/
theorem isZeroAt_hom_app {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules} (φ : M ⟶ M')
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X) (h : IsZeroAt s x) :
    IsZeroAt (φ.app ⊤ s) x := by
  have hgerm : (M'.presheaf.germ ⊤ x trivial).hom (φ.app ⊤ s) =
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x φ ((M.presheaf.germ ⊤ x trivial).hom s) :=
    (AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ X x φ ⊤ trivial s).symm
  have h' : (M.presheaf.germ ⊤ x trivial).hom s ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x)) := h
  have hle : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x)) ≤
      Submodule.comap (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x φ)
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (M'.presheaf.stalk x))) := by
    refine Submodule.smul_le.2 (fun r hr n _ => ?_)
    rw [Submodule.mem_comap, LinearMap.map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  show (M'.presheaf.germ ⊤ x trivial).hom (φ.app ⊤ s) ∈ _
  rw [hgerm]
  exact hle h'

/-- **`IsZeroAt` is invariant under isomorphisms of sheaves of modules.**

Proof.
1. `IsZeroAt s x` says: the germ `germ_x s ∈ M_x` (stalk of the underlying presheaf of modules at `x`)
   lies in `𝔪_x • M_x`, where `𝔪_x` is the maximal ideal of `O_{X,x}`.
2. A morphism `φ : M ⟶ M'` of sheaves of `O_X`-modules induces an `O_{X,x}`-linear map on stalks
   `φ_x : M_x → M'_x` with `φ_x (germ_x s) = germ_x (φ_⊤ s)` (naturality of germs:
   `TopCat.Presheaf.germ` commutes with the presheaf morphism `φ.val.presheaf`, i.e.
   `TopCat.Presheaf.stalkFunctor_map_germ_apply`). `O_{X,x}`-linearity means
   `φ_x (a • m) = a • φ_x m` for `a ∈ O_{X,x}` (`PresheafOfModules.stalkMap`-type linearity; the
   stalk of a presheaf of modules is an `O_{X,x}`-module via the colimit, and the stalk map is
   the colimit of the linear maps `φ_U`).
3. Hence `φ_x` maps `𝔪_x • M_x` into `𝔪_x • M'_x` (`Submodule.map_smul''`:
   image of `I • N` under a linear map is `I • image N`, and `image ⊤ ≤ ⊤`). This gives the
   direction `IsZeroAt s x → IsZeroAt (φ s) x` for any morphism `φ`.
4. Apply step 3 to `θ.hom` for `→`, and to `θ.inv` for `←`, using `θ.inv.app ⊤ (θ.hom.app ⊤ s) = s`
   (`Iso.hom_inv_id` applied at `⊤`).

Step 3 is `isZeroAt_hom_app`. -/
theorem isZeroAt_iso_iff {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules} (θ : M ≅ M')
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X) :
    IsZeroAt (θ.hom.app ⊤ s) x ↔ IsZeroAt s x := by
  refine ⟨fun h => ?_, isZeroAt_hom_app θ.hom s x⟩
  have h2 := isZeroAt_hom_app θ.inv _ x h
  have hinv : θ.inv.app ⊤ (θ.hom.app ⊤ s) = s :=
    congrArg (fun f : M ⟶ M => f.app ⊤ s) θ.hom_inv_id
  rw [hinv] at h2
  exact h2

end
