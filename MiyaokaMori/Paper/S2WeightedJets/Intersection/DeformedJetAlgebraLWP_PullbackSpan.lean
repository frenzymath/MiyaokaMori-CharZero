import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange

/-! # Sections of a pullback over an affine open are spanned by pulled-back sections (Stacks 01I9, span form)

Helper module for `reesDeformation_isLocallyWeightedPolynomial`.

* `Hom.appLinearMap`: the `Γ(X, U)`-linear map on sections induced by a morphism of module sheaves (`Hom.appLin` of
  `DeformedJetAlgebraLocallyWeightedPolynomial` is an `abbrev` for it).
* `mem_span_range_pullbackSectionsOn` (private copy of the lemma of the same name in `Stacks02k4Affine`; Stacks 01I9,
  `isIso_transpose_pullbackSectionsNative`): for `M` quasi-coherent on
  `X`, `U ⊆ X` affine and `V ⊆ g⁻¹U` affine, every section of `g^*M` over `V` is a `Γ(V)`-linear combination of pulled-back
  sections `(g^*s)|_V`, `s ∈ Γ(U, M)`.
* `range_pullback_map_appLinearMap_eq_span`: for `f : M ⟶ N` with `M` quasi-coherent, the image of `Γ(V, g^*f)` is the `Γ(V)`-span
  of the pullbacks of the image of `Γ(U, f)` (naturality of the section pullback in the module).
* `MvPolynomial.span_map_image_span`: base change of spans of sets of polynomials along `MvPolynomial.map`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The `Γ(X, U)`-linear map on sections induced by a morphism of module sheaves (`Hom.app` is only additive;
`Hom.app_smul` supplies linearity). -/
def Hom.appLinearMap {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := (φ.app U).hom
  map_add' := (φ.app U).hom.map_add
  map_smul' r a := AlgebraicGeometry.Scheme.Modules.Hom.app_smul φ r a

@[simp] theorem Hom.appLinearMap_apply {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    Hom.appLinearMap φ U s = φ.app U s := rfl

variable {Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X)

/-- Naturality of the section pullback in the module: `(g^*f)((g^*s)|_V) = (g^*(f s))|_V`
(adjunction unit naturality + naturality of `Hom.app` with respect to restriction). -/
theorem pullback_map_app_pullbackSectionsOn_lwp {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ g ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback g).map f).app V (pullbackSectionsOn g M U V h s) =
      pullbackSectionsOn g N U V h (f.app U s) := by
  rw [pullbackSectionsOn_apply, pullbackSectionsOn_apply]
  have h1 := ((AlgebraicGeometry.Scheme.Modules.pullback g).map f).mapPresheaf.naturality_apply
    (homOfLE h).op (pullbackUnitHom g M U s)
  have h2 := congrArg
    (fun ψ : M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N) => ψ.app U s)
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit_naturality f)
  simp only [AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.pushforward_map_app] at h2
  exact h1.trans (congrArg _ h2)

/-- **Stacks 01I9 in span form**: for `M` quasi-coherent, `U` affine and `V ⊆ g⁻¹U` affine, every section of `g^*M` over `V`
is a `Γ(V)`-linear combination of pulled-back sections `(g^*s)|_V`. From `isIso_transpose_pullbackSectionsNative`
(`Γ(V) ⊗_{Γ(U)} Γ(U, M) ≅ Γ(V, g^*M)`, `b ⊗ s ↦ b • (g^*s)|_V`) by induction on tensors.
The same statement is `Scheme.Modules.mem_span_range_pullbackSectionsOn` in `Stacks/Morphisms/Stacks02k4Affine.lean`
(which imports the `Ω` machinery); this local copy is `private` to keep the import closure of the Rees-deformation modules
small and to avoid the duplicate global name. -/
private theorem mem_span_range_pullbackSectionsOn (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {V : Y.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) (h : V ≤ g ⁻¹ᵁ U)
    (z : Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, V)) :
    z ∈ Submodule.span Γ(Y, V) (Set.range (pullbackSectionsOn g M U V h)) := by
  let _ : Algebra Γ(X, U) Γ(Y, V) := (g.appLE U V h).hom.toAlgebra
  have := isIso_transpose_pullbackSectionsNative g M U hU V hV h
  let F : TensorProduct Γ(X, U) Γ(Y, V) Γ(M, U) →ₗ[Γ(Y, V)]
      Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, V) :=
    (((ModuleCat.extendRestrictScalarsAdj (g.appLE U V h).hom).homEquiv _ _).symm
      (pullbackSectionsNative g M U V h)).hom
  have hb : Function.Bijective F := ConcreteCategory.bijective_of_isIso
    (((ModuleCat.extendRestrictScalarsAdj (g.appLE U V h).hom).homEquiv _ _).symm (pullbackSectionsNative g M U V h))
  obtain ⟨t, rfl⟩ := hb.2 z
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul b s =>
    show b • pullbackSectionsOn g M U V h s ∈ _
    exact Submodule.smul_mem _ b (Submodule.subset_span ⟨s, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- The image of `Γ(V, g^*f)` (`f : M ⟶ N`, `M` quasi-coherent, `U`, `V ⊆ g⁻¹U` affine) is the `Γ(V)`-span of the pullbacks
of the image of `Γ(U, f)`. -/
theorem range_pullback_map_appLinearMap_eq_span {M N : X.Modules} [M.IsQuasicoherent] (f : M ⟶ N) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {V : Y.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) (h : V ≤ g ⁻¹ᵁ U) :
    LinearMap.range (Hom.appLinearMap ((AlgebraicGeometry.Scheme.Modules.pullback g).map f) V) =
      Submodule.span Γ(Y, V) (pullbackSectionsOn g N U V h '' Set.range (f.app U)) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    have hy := mem_span_range_pullbackSectionsOn g M hU hV h y
    rw [Hom.appLinearMap_apply]
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      rw [pullback_map_app_pullbackSectionsOn_lwp]
      exact Submodule.subset_span ⟨f.app U s, ⟨s, rfl⟩, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [Hom.app_smul]; exact Submodule.smul_mem _ r hx
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨pullbackSectionsOn g M U V h s, by rw [Hom.appLinearMap_apply, pullback_map_app_pullbackSectionsOn_lwp]⟩

end AlgebraicGeometry.Scheme.Modules

namespace MvPolynomial

variable {σ : Type*} {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A)

/-- Base change of spans: `span_A (map f '' span_R s) = span_A (map f '' s)` (`map f` is `f`-semilinear:
`map f (r • x) = f r • map f x`). -/
theorem span_map_image_span (s : Set (MvPolynomial σ R)) :
    Submodule.span A (MvPolynomial.map f '' (Submodule.span R s : Set (MvPolynomial σ R))) =
      Submodule.span A (MvPolynomial.map f '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
      exact Submodule.smul_mem _ (f r) hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

end MvPolynomial

end
