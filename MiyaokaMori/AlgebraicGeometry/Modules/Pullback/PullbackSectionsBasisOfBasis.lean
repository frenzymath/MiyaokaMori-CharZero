import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Pullback of a basis of sections over an affine open

Sections of a pullback over the preimage of a trivialising affine open: for `p : T ⟶ B` affine,
`W` quasi-coherent on `B`, `U ⊆ B` affine open and `b` a finite basis of the `Γ(B, U)`-module
`Γ(W, U)`, the pulled-back sections `η_U(b i)` (`η` the unit `W ⟶ p_* p^* W` of the
pullback–pushforward adjunction, evaluated on `U`) form a basis of the `Γ(T, p⁻¹U)`-module
`Γ(p^* W, p⁻¹U)`. In words: `p^*` of a free module with basis `b` is free with basis `p^* b`.

Source: Stacks 01I9 (`Γ(V, g^*F) = Γ(V) ⊗_{Γ(U)} Γ(U, F)` for `g : V → U` affine schemes and
`F` quasi-coherent) together with `Module.Basis.baseChange`; alternatively Hartshorne II.5.2(e) and
the fact that pullback preserves free sheaves.

The proof uses `isIso_transpose_pullbackSectionsNative` (Stacks 01I9 in the form with the canonical
map): base change of the basis along the transpose.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

/-- Pullback of a free module on an affine open is free on
the pulled-back basis: `Γ(p^*W, p⁻¹U)` has the `Γ(T, p⁻¹U)`-basis `i ↦ η_U(b i)`, where
`η : W ⟶ p_* p^* W` is the adjunction unit and `b` is a `Γ(B, U)`-basis of `Γ(W, U)`.

Proof. Write `R := Γ(B, U)`, `S := Γ(T, p⁻¹U)`
(an `R`-algebra through `p^♯ = p.appLE U (p⁻¹U)`), `N := Γ(W, U)` (free over `R` with basis `b`).

Route B (Stacks 01I9, the route formalized). `p⁻¹U` is affine because `p` is an affine morphism
(`IsAffineOpen.preimage`). By `isIso_transpose_pullbackSectionsNative p W U (p⁻¹U)`
(Stacks 01I9 in the form with the canonical map), the
`S`-linear map `S ⊗_R N → Γ(p^*W, p⁻¹U)`, `t ⊗ s ↦ t • (η_U s)|_{p⁻¹U}`, is an isomorphism; here the
restriction from `p⁻¹U` to itself is the identity (`presheaf.map_id`), so `1 ⊗ b i ↦ η_U(b i)`.
The base change of a basis is a basis (`Module.Basis.baseChange b S : Basis I S (S ⊗_R N)`,
`baseChange_apply : (b.baseChange S) i = 1 ⊗ₜ b i`); transporting it along the isomorphism
(`Module.Basis.map`) gives the required basis `c` with `c i = η_U(b i)`.

Route A (free sheaves, no 01I9). (1) `W|_U ≅ O_U^{⊕I}` with the generator `i` corresponding to `b i`
(`W` quasi-coherent, `U` affine, `b` a basis of global sections: the canonical map
`free I ⟶ W|_U` from the sections `b i` is an isomorphism, transported to `U` through `U.isoSpec`,
or `pullback_iso_free_of_basis`). (2) Pullback along the restriction `p' := p.resLE U (p⁻¹U)` of a free
sheaf is free on the pulled-back generators (`pullbackObjFreeIso`, compatible with `ιFree`), and `(p^*W)|_{p⁻¹U} ≅ p'^*(W|_U)` (`pullbackComp` along
the square `(p⁻¹U).ι ≫ p = p' ≫ U.ι`, `Scheme.Hom.resLE_comp_ι`). (3) The unit `η` is compatible with
these identifications: the section `η_U(b i)` restricted to `p⁻¹U` corresponds to the `i`-th generator of
`free I` on `p⁻¹U`. (4) `Γ(p⁻¹U, free I) = I → Γ(T, p⁻¹U)` for finite `I` (finite coproduct = biproduct,
`Γ` additive; `MiyaokaMori.DualPullback.coord_bijective`), whose standard basis is the family of
generators. Steps (3)–(4) are bookkeeping with `restrictFunctorIsoPullback` and `pullbackComp`.

Route B needs only `isIso_transpose_pullbackSectionsNative` (in turn reduced to
`pullbackSectionsTensorMap_bijective`) plus `Module.Basis.baseChange` (Mathlib). Route A would need
the compatibility of the adjunction unit with `pullbackComp`/`restrictFunctorIsoPullback`.

Edge cases: `I` empty — `W|_U = 0`, both sides `0`, the empty family is a basis; `U = ∅` — `Γ(B, ∅) = 0`
is the zero ring, every module over it is trivial, `Γ(T, ∅) = 0` likewise, and any family indexed by `I`
is a basis of the zero module over the zero ring only if `I` is empty — but over the zero ring
`Module.Basis` still exists for any `I` (all modules over the zero ring are subsingletons and
`Finsupp I 0` is also a subsingleton), so the statement holds; `T = ∅` similar. -/
theorem AlgebraicGeometry.Scheme.Modules.pullback_sections_exists_basis {T B : AlgebraicGeometry.Scheme.{u}}
    (p : T ⟶ B) [AlgebraicGeometry.IsAffineHom p] (W : B.Modules) [W.IsQuasicoherent]
    (U : B.affineOpens) {I : Type u} [Finite I] (b : Module.Basis I Γ(B, U.1) Γ(W, U.1)) :
    ∃ c : Module.Basis I Γ(T, p ⁻¹ᵁ U.1) Γ((AlgebraicGeometry.Scheme.Modules.pullback p).obj W, p ⁻¹ᵁ U.1),
      ∀ i, c i = ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p).unit.app W).app U.1 (b i) := by
  have hU' : AlgebraicGeometry.IsAffineOpen (p ⁻¹ᵁ U.1) := U.2.preimage p
  have hiso := AlgebraicGeometry.Scheme.Modules.isIso_transpose_pullbackSectionsNative p W U.1 U.2
    (p ⁻¹ᵁ U.1) hU' le_rfl
  set t := ((ModuleCat.extendRestrictScalarsAdj (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom).homEquiv _ _).symm
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionsNative p W U.1 (p ⁻¹ᵁ U.1) le_rfl) with ht
  have hbij : Function.Bijective t.hom := ConcreteCategory.bijective_of_isIso t
  letI : Algebra Γ(B, U.1) Γ(T, p ⁻¹ᵁ U.1) := (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  let e : (Γ(T, p ⁻¹ᵁ U.1) ⊗[Γ(B, U.1)] Γ(W, U.1)) ≃ₗ[Γ(T, p ⁻¹ᵁ U.1)]
      Γ((AlgebraicGeometry.Scheme.Modules.pullback p).obj W, p ⁻¹ᵁ U.1) :=
    LinearEquiv.ofBijective t.hom hbij
  refine ⟨(b.baseChange Γ(T, p ⁻¹ᵁ U.1)).map e, fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply]
  simp only [e]
  change (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionsNative p W U.1 (p ⁻¹ᵁ U.1) le_rfl)).hom
      ((1 : Γ(T, p ⁻¹ᵁ U.1)) ⊗ₜ[Γ(B, U.1)] b i) = _
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
  change (1 : Γ(T, p ⁻¹ᵁ U.1)) •
    AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn p W U.1 (p ⁻¹ᵁ U.1) le_rfl (b i) = _
  rw [one_smul, AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_apply]
  have h0 : (homOfLE (le_refl (p ⁻¹ᵁ U.1))).op = 𝟙 (op (p ⁻¹ᵁ U.1)) := rfl
  rw [h0, CategoryTheory.Functor.map_id]
  rfl


end
