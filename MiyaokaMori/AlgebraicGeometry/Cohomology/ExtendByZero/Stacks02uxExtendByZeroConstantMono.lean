import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02uxAux
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02uzExtendByZero
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02uxExtendByZeroDesc

/-! # `j_!ℤ_U` is a subsheaf of the constant sheaf

`j_!ℤ_U` is a subsheaf of the constant sheaf `ℤ_X`: there is a monomorphism `j_!ℤ_U ⟶ ℤ_X`
(Stacks 02UX, third paragraph: "`K` is a subsheaf of `j_!ℤ_U ⊂ ℤ_X`").

Source: Stacks 02UX (cohomology-lemma-vanishing-generated-one-section); Stacks 00A5 (sheaves-lemma-j-shriek-abelian),
the adjunction `j_! ⊣ j^{-1}`.

Proved via `extendByZeroDesc` / `extendByZeroDesc_mono_of_isIso` from `Stacks02uxExtendByZeroDesc.lean`,
applied to `α = (restrictConstantSheafIso U _).inv : ℤ_U ≅ (ℤ_X)|_U`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

/-- (Stacks 02UX, third paragraph; Stacks 00A5.) For an open `U ⊆ X` there is a monomorphism of
abelian sheaves `j_!ℤ_U ⟶ ℤ_X`, where `ℤ_U`, `ℤ_X` are the constant sheaves with value `ULift ℤ` and
`j_!ℤ_U = TopCat.Sheaf.extendByZeroConstant U`.

**Natural-language proof (self-contained).**

*Step 1 (the morphism; the transpose along `j_! ⊣ j^{-1}`; now `TopCat.Sheaf.extendByZeroDesc` in
`Stacks02uxExtendByZeroDesc.lean`).* Let `j : U ↪ X`. By
definition `j_!G` (`TopCat.Sheaf.extendByZero U G`) is the sheafification of the presheaf `P` with
`P(V) = G(j^{-1}V)` if `V ⊆ U` and `P(V) = 0` otherwise (`extendByZeroPresheaf`, `extendByZero_eq_sheafify` is
`rfl`; `P(V)` is the subgroup `extendByZeroSubgroup U G V` of `(j_*G)(V) = G(j^{-1}V)`). Given any abelian sheaf
`F` on `X` and a morphism `α : G ⟶ F|_U` (`F|_U = TopCat.Sheaf.restrict F U`, the naive pullback, with
`(F|_U)(W) = F(j(W))`), define `P ⟶ F.val` componentwise: for `V ⊆ U` it is `α_{j^{-1}V} : G(j^{-1}V) ⟶
F(j(j^{-1}V)) = F(V)` (`j(j^{-1}V) = V ∩ U = V`, so `F.map` of the equality `eqToHom`/`homOfLE`), and for `V ⊄ U`
it is `0` (the source is the zero subgroup). Naturality: for `V' ⊆ V ⊆ U` it is the naturality of `α` (on
`j^{-1}V' ⊆ j^{-1}V`) plus functoriality of `F`; if `V ⊄ U` then `P(V) = 0` and both composites vanish; the case
`V ⊆ U`, `V' ⊄ U` cannot occur. Sheafify: `extendByZeroDesc α := presheafToSheaf.map (P ⟶ F.val) ≫
(sheafificationAdjunction _ _).counit.app F : j_!G ⟶ F`. Apply this with `G = ℤ_U`, `F = ℤ_X`, and
`α := (restrictConstantSheafIso U (AddCommGrpCat.of (ULift ℤ))).inv : ℤ_U ≅ (ℤ_X)|_U` (proved in
`Stacks02uzExtendByZero.lean`), obtaining `m : j_!ℤ_U ⟶ ℤ_X`.

*Step 2 (`m` is a monomorphism; `extendByZeroDesc_mono_of_isIso`, via `extendByZeroDesc_comp_restrictUnit`).* Let `η : ℤ_X ⟶ j_*((ℤ_X)|_U)` be the unit of the adjunction
`restrictPushforwardAdjunction U` (`j^{-1} ⊣ j_*`, proved in `Stacks02uzExtendByZero.lean`), and
`j_*α : j_*ℤ_U ⟶ j_*((ℤ_X)|_U)` (an isomorphism, as `α` is). Claim: `m ≫ η = extendByZeroToPushforward ℤ_U ≫ j_*α`
as morphisms `j_!ℤ_U ⟶ j_*((ℤ_X)|_U)`. Both sides are morphisms out of a sheafification, so by the adjunction
`sheafificationAdjunction` (`Sheaf.hom_ext` after precomposing with `toSheafify`; equivalently
`(sheafificationAdjunction _ _).homEquiv` is a bijection) it suffices to compare them on the presheaf `P`: at
`V ⊆ U` both send `x ∈ P(V) = ℤ_U(j^{-1}V)` to `α_{j^{-1}V}(x)` viewed in `(j_*((ℤ_X)|_U))(V) = (ℤ_X)|_U(j^{-1}V) =
ℤ_X(V)` — on the left because `η_V : ℤ_X(V) → ℤ_X(j(j^{-1}V))` is `ℤ_X.map` of the equality `V = j(j^{-1}V)`, on
the right by definition of `j_*α`; at `V ⊄ U` both vanish on `P(V) = 0`. Now `extendByZeroToPushforward ℤ_U` is a
monomorphism (`extendByZeroToPushforward_mono`, sheafification is left exact) and `j_*α` is an isomorphism, so the
right-hand side is a monomorphism, hence so is `m` (`mono_of_mono_fac`: if `m ≫ η` is mono then `m` is mono).

*Alternative (stalks).* `m` is a monomorphism iff it is injective on stalks (`TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective` / `Sheaf` mono iff stalkwise mono); at `x ∈ U` the stalk map is
`(j_!ℤ_U)_x ≅ (ℤ_U)_x ≅ ℤ ≅ (ℤ_X)_x` (`extendByZero_stalk_of_mem`) and at `x ∉ U` the source stalk is `0`
(`isZero_extendByZero_stalk_of_notMem`). The route of Step 2 does not need these stalk computations.

**Edge cases.** `U = ∅`: `j_!ℤ_∅ = 0` (`isZero_extendByZero_of_isZero`, since every sheaf on `∅` is zero), and
`0 ⟶ ℤ_X` is mono. `U = X`: `m` is the isomorphism `j_!ℤ_X ≅ ℤ_X`. `X = ∅`: everything is zero. Only Prop is
asserted (existence of a mono); no data leaves this lemma. -/
theorem TopCat.Sheaf.exists_mono_extendByZeroConstant_to_constant {X : TopCat.{u}} (U : Opens X) :
    ∃ m : TopCat.Sheaf.extendByZeroConstant U ⟶
      (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ)), CategoryTheory.Mono m :=
  ⟨TopCat.Sheaf.extendByZeroDesc U (TopCat.Sheaf.restrictConstantSheafIso U (AddCommGrpCat.of (ULift ℤ))).inv,
    TopCat.Sheaf.extendByZeroDesc_mono_of_isIso U _⟩

end
