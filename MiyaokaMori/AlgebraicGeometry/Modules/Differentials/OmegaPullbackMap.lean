import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaUniversalDerivation
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaOpenImmersionSquare
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.IsIsoOfAffineOpensCoverBijective
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange

/-! # The pullback map of relative differentials

A commutative square `g ≫ p = q ≫ b` gives a map `g^*Ω_{Z/C} → Ω_{W/C'}` (Stacks 01UV), obtained
from the derivation `d_{W/C'} ∘ g^♯` through the universal property of `Ω` and the
pullback–pushforward adjunction; for a fibre-product square it is an isomorphism (Stacks 01V0).

References: Stacks 01UV (functoriality of differentials), 01V0 (base change).

The derivation `pushforwardDerivation` is literally `Omega.squarePushDerivation p q g b h.symm`
(bridge `pushforwardDerivation_eq_squarePushDerivation`, `rfl`). The base-change theorem
`pullbackMap_isIso_of_isPullback` is assembled from five named lemmas (see the section
"Base change (Stacks 01V0): the pieces"): it stays at the level of sections over affine opens
`W₀ = g⁻¹Z₀ ⊓ q⁻¹C'₀` and uses Mathlib's `Scheme.Hom.isPullback_resLE` /
`isIso_pushoutSection_of_isAffineOpen` (the restricted square is a fibre product and the coordinate
rings form a pushout) together with `isIso_of_affineOpens_cover_bijective` (Stacks 01AI + 01I6).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The universal derivation `d : O_X → Ω_{X/S}` (the value of `Omega.homEquivDerivation` at the
identity). -/

/-! ## The components of `pushforwardDerivation` and its three proof obligations

The `d` field of the structure is the top-level `pushforwardDerivationMap`; the three proof
obligations are the named theorems preceding the definition. -/

/-- `g_*Ω_{W/C'}`, viewed over the base ring functor `Z.presheaf ⋙ forget₂ CommRingCat RingCat`
required by `Derivation'` (`Z.ringCatSheaf.obj` is this by definition; the abbreviation only makes
the `a • x` in the statements of the three obligations below findable by instance search). -/
noncomputable abbrev AlgebraicGeometry.Omega.pushforwardOmega
    {W Z C' : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ Z) (q : W ⟶ C') :
    PresheafOfModules.{u} (Z.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat.{u}) :=
  ((AlgebraicGeometry.Scheme.Modules.pushforward g).obj (AlgebraicGeometry.Omega q)).val

/-- The underlying additive map of the derivation: `U ↦ d_{W/C'}(g⁻¹U) ∘ g^♯(U)`. -/
noncomputable def AlgebraicGeometry.Omega.pushforwardDerivationMap
    {W Z C' : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ Z) (q : W ⟶ C') (U : (Z.Opens)ᵒᵖ) :
    (Z.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat.{u}).obj U →+
      (AlgebraicGeometry.Omega.pushforwardOmega g q).obj U :=
  ((AlgebraicGeometry.Omega.universalDerivation q).d
    (X := Opposite.op (g ⁻¹ᵁ U.unop))).comp (g.app U.unop).hom.toAddMonoidHom

/-- The Leibniz rule `d(ab) = a·db + b·da` (Stacks 01UV); it reduces to the Leibniz rule of the
universal derivation of `Ω_{W/C'}`.

Proof: `pushforwardDerivationMap g q U = d_{W/C'}(g⁻¹U) ∘ g^♯(U)` with `g^♯(U)` a ring homomorphism,
so `d(ab) = d_{W/C'}(g^♯ a · g^♯ b) = g^♯ a • d_{W/C'}(g^♯ b) + g^♯ b • d_{W/C'}(g^♯ a)`
(`Derivation.d_mul`), and the `Γ(Z, U)`-module structure of `g_*Ω_{W/C'}` on `U` is obtained by
restricting scalars along `g^♯(U)`, so `g^♯ a • x = a • x`. -/
theorem AlgebraicGeometry.Omega.pushforwardDerivation_d_mul
    {W Z C' : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ Z) (q : W ⟶ C')
    {U : (Z.Opens)ᵒᵖ} (a b : (Z.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat.{u}).obj U) :
    AlgebraicGeometry.Omega.pushforwardDerivationMap g q U (a * b) =
      a • AlgebraicGeometry.Omega.pushforwardDerivationMap g q U b +
        b • AlgebraicGeometry.Omega.pushforwardDerivationMap g q U a := by
  exact (congrArg ((AlgebraicGeometry.Omega.universalDerivation q).d (X := Opposite.op (g ⁻¹ᵁ U.unop)))
    (map_mul (g.app U.unop).hom a b)).trans
    ((AlgebraicGeometry.Omega.universalDerivation q).d_mul (X := Opposite.op (g ⁻¹ᵁ U.unop)) _ _)

/-- Compatibility with restriction: `d` commutes with the restriction maps of the presheaf
(Stacks 01UV).

Proof: for `f : U ⟶ V`, `g^♯` commutes with restriction (naturality of `Scheme.Hom.app`,
`g.naturality f`), `d_{W/C'}` commutes with restriction (`Derivation.d_map`), and the restriction
of `g_*Ω_{W/C'}` is by definition the restriction of `Ω_{W/C'}` along `g⁻¹f`. -/
theorem AlgebraicGeometry.Omega.pushforwardDerivation_d_map
    {W Z C' : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ Z) (q : W ⟶ C')
    {U V : (Z.Opens)ᵒᵖ} (f : U ⟶ V)
    (x : (Z.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat.{u}).obj U) :
    AlgebraicGeometry.Omega.pushforwardDerivationMap g q V
        ((Z.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat.{u}).map f x) =
      (AlgebraicGeometry.Omega.pushforwardOmega g q).map f
        (AlgebraicGeometry.Omega.pushforwardDerivationMap g q U x) := by
  have hn : (g.app V.unop).hom (Z.presheaf.map f x) =
      W.presheaf.map ((Opens.map g.base).map f.unop).op ((g.app U.unop).hom x) :=
    congrArg (fun t => t.hom x) (g.naturality f)
  exact (congrArg ((AlgebraicGeometry.Omega.universalDerivation q).d (X := Opposite.op (g ⁻¹ᵁ V.unop))) hn).trans
    ((AlgebraicGeometry.Omega.universalDerivation q).d_map (X := Opposite.op (g ⁻¹ᵁ U.unop))
      ((Opens.map g.base).map f.unop).op _)

/-- Vanishing on the image of `p⁻¹O_C` — this is where the commutativity of the square
`g ≫ p = q ≫ b` is used (Stacks 01UV).

Proof: an element of the image is of the form `p.appLE V U r` (`inverseImageStructureMap_app_eq_appLE`);
by `appLE_comp_appLE` and the commutative square, `g^♯(p.appLE V U r)` is `(q ≫ b).appLE V (g⁻¹U) r`,
which factors through `q⁻¹O_{C'}`, on whose image `d_{W/C'}` vanishes (`Omega.derivation_appLE`).
This is the `d_app` field of `Omega.squarePushDerivation p q g b h.symm`. -/
theorem AlgebraicGeometry.Omega.pushforwardDerivation_d_app
    {W Z C C' : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ Z) (p : Z ⟶ C) (q : W ⟶ C') (b : C' ⟶ C) (_h : g ≫ p = q ≫ b)
    {U : (Z.Opens)ᵒᵖ} (a : (AlgebraicGeometry.Scheme.inverseImagePresheaf p).obj U) :
    AlgebraicGeometry.Omega.pushforwardDerivationMap g q U
        ((AlgebraicGeometry.Scheme.inverseImageStructureMap p).app U a) = 0 :=
  (AlgebraicGeometry.Omega.squarePushDerivation p q g b _h.symm).d_app a

/- A commutative square `g ≫ p = q ≫ b` (`g : W → Z`, `p : Z → C`, `q : W → C'`, `b : C' → C`) gives a
   `p`-derivation from `O_Z` to `g_*Ω_{W/C'}`: `U ↦ d_{W/C'}(g⁻¹U) ∘ g^♯(U)`. The three obligations
   (Leibniz rule, compatibility with restriction, vanishing on `p⁻¹O_C`, the last using the square)
   are the named theorems `pushforwardDerivation_d_mul` / `_d_map` / `_d_app`. -/

noncomputable def AlgebraicGeometry.Omega.pushforwardDerivation {W Z C C' : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ Z) (p : Z ⟶ C) (q : W ⟶ C') (b : C' ⟶ C) (_h : g ≫ p = q ≫ b) :
    (((AlgebraicGeometry.Scheme.Modules.pushforward g).obj (AlgebraicGeometry.Omega q)).val).Derivation'
      (AlgebraicGeometry.Scheme.inverseImageStructureMap p) where
  d {U} := AlgebraicGeometry.Omega.pushforwardDerivationMap g q U
  d_mul := AlgebraicGeometry.Omega.pushforwardDerivation_d_mul g q
  d_map := AlgebraicGeometry.Omega.pushforwardDerivation_d_map g q
  d_app := AlgebraicGeometry.Omega.pushforwardDerivation_d_app g p q b _h

/-- `pushforwardDerivation` and `Omega.squarePushDerivation` (with the square written as
`q ≫ b = g ≫ p`) are the same derivation (definitionally). -/
theorem AlgebraicGeometry.Omega.pushforwardDerivation_eq_squarePushDerivation
    {W Z C C' : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ Z) (p : Z ⟶ C) (q : W ⟶ C') (b : C' ⟶ C) (h : g ≫ p = q ≫ b) :
    AlgebraicGeometry.Omega.pushforwardDerivation g p q b h =
      AlgebraicGeometry.Omega.squarePushDerivation p q g b h.symm := rfl

/- The pullback map of differentials `g^*Ω_{Z/C} → Ω_{W/C'}` (Stacks 01UV): the derivation above gives
   `Ω_{Z/C} → g_*Ω_{W/C'}` by the universal property; then take the adjoint transpose. -/

noncomputable def AlgebraicGeometry.Omega.pullbackMap {W Z C C' : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ Z) (p : Z ⟶ C) (q : W ⟶ C') (b : C' ⟶ C) (h : g ≫ p = q ≫ b) :
    (AlgebraicGeometry.Scheme.Modules.pullback g).obj (AlgebraicGeometry.Omega p) ⟶ AlgebraicGeometry.Omega q :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    ((AlgebraicGeometry.Omega.homEquivDerivation p _).symm
      (AlgebraicGeometry.Omega.pushforwardDerivation g p q b h))

/-- `pullbackMap` is the adjoint transpose of `Omega.squareToPushforward` (`Ω_{Z/C} → g_*Ω_{W/C'}`). -/
theorem AlgebraicGeometry.Omega.pullbackMap_eq_squareToPushforward
    {W Z C C' : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ Z) (p : Z ⟶ C) (q : W ⟶ C') (b : C' ⟶ C) (h : g ≫ p = q ≫ b) :
    AlgebraicGeometry.Omega.pullbackMap g p q b h =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
        (AlgebraicGeometry.Omega.squareToPushforward p q g b h.symm) := rfl

/-- The pullback map on generators: the adjunction unit followed by `pullbackMap` sends `d_{Z/C} a`
to `d_{W/C'}(g^♯ a)`. -/
theorem AlgebraicGeometry.Omega.pullbackMap_unit_app_d
    {W Z C C' : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ Z) (p : Z ⟶ C) (q : W ⟶ C') (b : C' ⟶ C) (h : g ≫ p = q ≫ b)
    (U : Z.Opens) (a : Γ(Z, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pushforward g).map (AlgebraicGeometry.Omega.pullbackMap g p q b h)).app U
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (AlgebraicGeometry.Omega p)).app U
          ((AlgebraicGeometry.Omega.universalDerivation p).d (X := Opposite.op U) a)) =
      (AlgebraicGeometry.Omega.universalDerivation q).d (X := Opposite.op (g ⁻¹ᵁ U)) ((g.app U).hom a) := by
  have h1 : AlgebraicGeometry.Omega.squareToPushforward p q g b h.symm =
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (AlgebraicGeometry.Omega p) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward g).map (AlgebraicGeometry.Omega.pullbackMap g p q b h) := by
    rw [AlgebraicGeometry.Omega.pullbackMap_eq_squareToPushforward, Adjunction.homEquiv_symm_apply]
    simp
  have h2 := AlgebraicGeometry.Omega.squareToPushforward_app_d p q g b h.symm U a
  rw [h1] at h2
  exact h2

/-! ## Base change (Stacks 01V0): the pieces

The proof of `pullbackMap_isIso_of_isPullback` below is assembled from five named lemmas, all at the
level of sections over affine opens, so that no isomorphism of module sheaves has to be tracked:
1. `Omega.isAffineOpen_inf_preimage_of_isPullback`: `W₀ := g⁻¹Z₀ ⊓ q⁻¹C'₀` is affine when
   `C₀ ⊆ C`, `Z₀ ⊆ p⁻¹C₀`, `C'₀ ⊆ b⁻¹C₀` are affine (Mathlib `Scheme.Hom.isPullback_resLE`:
   the restricted square is again a fibre-product square, so `W₀ ≅ Z₀ ×_{C₀} C'₀`).
2. `Omega.algebra_isPushout_of_isPullback`: `Γ(W₀) = Γ(C'₀) ⊗_{Γ(C₀)} Γ(Z₀)`
   (Mathlib `isIso_pushoutSection_of_isAffineOpen`, Stacks 01JQ for the restricted square).
3. `Scheme.Modules.pullbackSectionsOnTensorMap(_bijective)`: `Γ(W₀) ⊗_{Γ(Z₀)} Γ(M, Z₀) ≃ Γ(W₀, g^*M)`
   for quasi-coherent `M` (Stacks 01I9, open-set version; the bijectivity is
   `isIso_transpose_pullbackSectionsNative`).
4. `Omega.pullbackMap_app_pullbackSectionsOn_d`: the generator formula
   `pullbackMap (g^*(d a)|_{W₀}) = d (g^♯ a|_{W₀})`.
5. `Omega.pullbackMap_app_bijective_of_isPullback`: `pullbackMap.app W₀` is bijective, by comparing with
   Mathlib's `KaehlerDifferential.tensorKaehlerEquiv` through `Omega_appIso` (Stacks 01UT).
-/

namespace AlgebraicGeometry

section BaseChangePieces

variable {W Z C C' : Scheme.{u}} (g : W ⟶ Z) (p : Z ⟶ C) (q : W ⟶ C') (b : C' ⟶ C)

/-- For a fibre-product square `IsPullback g q p b` and affine opens `C₀ ⊆ C`, `Z₀ ⊆ p⁻¹C₀`,
`C'₀ ⊆ b⁻¹C₀`, the open `g⁻¹Z₀ ⊓ q⁻¹C'₀ ⊆ W` is affine: it is `Z₀ ×_{C₀} C'₀`
(Mathlib `Scheme.Hom.isPullback_resLE`), a fibre product of affine schemes. -/
theorem Omega.isAffineOpen_inf_preimage_of_isPullback (h : IsPullback g q p b)
    {C₀ : C.Opens} {Z₀ : Z.Opens} {C'₀ : C'.Opens}
    (hC₀ : IsAffineOpen C₀) (hZ₀ : IsAffineOpen Z₀) (hC'₀ : IsAffineOpen C'₀)
    (hZ : Z₀ ≤ p ⁻¹ᵁ C₀) (hC' : C'₀ ≤ b ⁻¹ᵁ C₀) :
    IsAffineOpen (g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) := by
  have : IsAffine _ := hC₀
  have : IsAffine _ := hZ₀
  have : IsAffine _ := hC'₀
  exact .of_isIso (Scheme.Hom.isPullback_resLE h hC' hZ rfl).isoPullback.hom

/-- Coordinate rings of the restricted fibre-product square (Stacks 01JQ): for a fibre-product square
`IsPullback g q p b`, affine opens `C₀ ⊆ C`, `Z₀ ⊆ p⁻¹C₀`, `C'₀ ⊆ b⁻¹C₀` and
`W₀ = g⁻¹Z₀ ⊓ q⁻¹C'₀`, the square of rings `Γ(C₀) → Γ(Z₀), Γ(C'₀) → Γ(W₀)` (all maps `appLE`) is a
pushout, i.e. `Γ(W₀) = Γ(C'₀) ⊗_{Γ(C₀)} Γ(Z₀)`. The algebra structures are taken as instances with
their `algebraMap`s specified by equations, so that the lemma can be used with any spelling of them.
Proof: Mathlib `isIso_pushoutSection_of_isAffineOpen` + `isIso_pushoutSection_iff` give the pushout
in `CommRingCat`; `CommRingCat.isPushout_iff_isPushout` turns it into `Algebra.IsPushout`. -/
theorem Omega.algebra_isPushout_of_isPullback (h : IsPullback g q p b)
    {C₀ : C.Opens} {Z₀ : Z.Opens} {C'₀ : C'.Opens} {W₀ : W.Opens}
    (hC₀ : IsAffineOpen C₀) (hZ₀ : IsAffineOpen Z₀) (hC'₀ : IsAffineOpen C'₀)
    (hZ : Z₀ ≤ p ⁻¹ᵁ C₀) (hC' : C'₀ ≤ b ⁻¹ᵁ C₀) (hW₀ : W₀ = g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)
    (hWZ : W₀ ≤ g ⁻¹ᵁ Z₀) (hWC' : W₀ ≤ q ⁻¹ᵁ C'₀)
    [Algebra Γ(C, C₀) Γ(Z, Z₀)] [Algebra Γ(C, C₀) Γ(C', C'₀)] [Algebra Γ(Z, Z₀) Γ(W, W₀)]
    [Algebra Γ(C', C'₀) Γ(W, W₀)] [Algebra Γ(C, C₀) Γ(W, W₀)]
    [IsScalarTower Γ(C, C₀) Γ(Z, Z₀) Γ(W, W₀)] [IsScalarTower Γ(C, C₀) Γ(C', C'₀) Γ(W, W₀)]
    (e₁ : algebraMap Γ(C, C₀) Γ(Z, Z₀) = (p.appLE C₀ Z₀ hZ).hom)
    (e₂ : algebraMap Γ(C, C₀) Γ(C', C'₀) = (b.appLE C₀ C'₀ hC').hom)
    (e₃ : algebraMap Γ(Z, Z₀) Γ(W, W₀) = (g.appLE Z₀ W₀ hWZ).hom)
    (e₄ : algebraMap Γ(C', C'₀) Γ(W, W₀) = (q.appLE C'₀ W₀ hWC').hom) :
    Algebra.IsPushout Γ(C, C₀) Γ(C', C'₀) Γ(Z, Z₀) Γ(W, W₀) := by
  subst hW₀
  have h1 := (isIso_pushoutSection_iff h hC' hZ rfl).mp
    (isIso_pushoutSection_of_isAffineOpen h hC' hZ rfl hC₀ hC'₀ hZ₀)
  refine (CommRingCat.isPushout_iff_isPushout.mp ?_).symm
  rw [e₁, e₂, e₃, e₄]
  exact h1

/-- A morphism of module sheaves commutes with restriction, on sections (variable-level form; needed
because `exact`ing the naturality square directly against the concrete `pullbackMap`/`Omega` terms
makes Lean unfold them). -/
theorem Omega.moduleHom_app_restrict {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {U U' : X.Opens} (e : U' ≤ U) (x : Γ(M, U)) :
    (φ.app U').hom (M.presheaf.map (homOfLE e).op x) =
      N.presheaf.map (homOfLE e).op ((φ.app U).hom x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE e).op) x

/-- Generator formula for the pullback map on sections over an open `W₀ ⊆ g⁻¹Z₀`:
`pullbackMap.app W₀ ((g^*(d_{Z/C} a))|_{W₀}) = d_{W/C'} (g^♯ a |_{W₀})`.
Proof: naturality of `pullbackMap` in the open, `pullbackMap_unit_app_d`, and `d_map`. -/
theorem Omega.pullbackMap_app_pullbackSectionsOn_d (h : g ≫ p = q ≫ b)
    {Z₀ : Z.Opens} {W₀ : W.Opens} (hWZ : W₀ ≤ g ⁻¹ᵁ Z₀) (a : Γ(Z, Z₀)) :
    ((Omega.pullbackMap g p q b h).app W₀).hom
        (Scheme.Modules.pullbackSectionsOn g (Omega p) Z₀ W₀ hWZ
          ((Omega.universalDerivation p).d (X := op Z₀) a)) =
      (Omega.universalDerivation q).d (X := op W₀) ((g.appLE Z₀ W₀ hWZ).hom a) := by
  have hnat : ((Omega.pullbackMap g p q b h).app W₀).hom
      (((Scheme.Modules.pullback g).obj (Omega p)).presheaf.map (homOfLE hWZ).op
        (Scheme.Modules.pullbackUnitHom g (Omega p) Z₀
          ((Omega.universalDerivation p).d (X := op Z₀) a))) =
      (Omega q).presheaf.map (homOfLE hWZ).op
        (((Omega.pullbackMap g p q b h).app (g ⁻¹ᵁ Z₀)).hom
          (Scheme.Modules.pullbackUnitHom g (Omega p) Z₀
            ((Omega.universalDerivation p).d (X := op Z₀) a))) := by
    exact Omega.moduleHom_app_restrict (Omega.pullbackMap g p q b h) hWZ _
  have h2 : ((Omega.pullbackMap g p q b h).app (g ⁻¹ᵁ Z₀)).hom
      (Scheme.Modules.pullbackUnitHom g (Omega p) Z₀
        ((Omega.universalDerivation p).d (X := op Z₀) a)) =
      (Omega.universalDerivation q).d (X := op (g ⁻¹ᵁ Z₀)) ((g.app Z₀).hom a) :=
    Omega.pullbackMap_unit_app_d g p q b h Z₀ a
  refine hnat.trans ?_
  refine (congrArg (fun t => ((Omega q).presheaf.map (homOfLE hWZ).op).hom t) h2).trans ?_
  exact ((Omega.universalDerivation q).d_map (X := op (g ⁻¹ᵁ Z₀)) (homOfLE hWZ).op _).symm

end BaseChangePieces

namespace Scheme.Modules

variable {Y X : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) (V : X.Opens) (V' : Y.Opens)
  (h : V' ≤ g ⁻¹ᵁ V)

/-- The canonical `Γ(Y, V')`-linear map `Γ(Y, V') ⊗_{Γ(X, V)} Γ(M, V) → Γ(g^*M, V')`,
`s ⊗ m ↦ s • (g^*m)|_{V'}` (Stacks 01I9, open-set version), for `V' ≤ g⁻¹V`; the algebra structure
`Γ(X, V) → Γ(Y, V')` is `g.appLE`. -/
def pullbackSectionsOnTensorMap :
    letI : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
    TensorProduct Γ(X, V) Γ(Y, V') Γ(M, V) →ₗ[Γ(Y, V')] Γ((pullback g).obj M, V') :=
  letI : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
  letI := Module.compHom Γ((pullback g).obj M, V') (algebraMap Γ(X, V) Γ(Y, V'))
  letI : IsScalarTower Γ(X, V) Γ(Y, V') Γ((pullback g).obj M, V') :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  LinearMap.liftBaseChange Γ(Y, V')
    { toFun := pullbackSectionsOn g M V V' h
      map_add' := map_add _
      map_smul' := fun r s ↦ pullbackSectionsOn_smul_native g M V V' h r s }

theorem pullbackSectionsOnTensorMap_tmul (s : Γ(Y, V')) (m : Γ(M, V)) :
    letI : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
    pullbackSectionsOnTensorMap g M V V' h (s ⊗ₜ m) = s • pullbackSectionsOn g M V V' h m := rfl

/-- **Stacks 01I9, open-set version**: for `V ⊆ X`, `V' ⊆ g⁻¹V` affine and `M` quasi-coherent, the
canonical map `Γ(Y, V') ⊗_{Γ(X, V)} Γ(M, V) → Γ(g^*M, V')` is bijective. This is a restatement of
`isIso_transpose_pullbackSectionsNative`: the two maps
agree on pure tensors (`s ⊗ m ↦ s • (g^*m)|_{V'}`, both by `rfl`). -/
theorem pullbackSectionsOnTensorMap_bijective [M.IsQuasicoherent]
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') :
    letI : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
    Function.Bijective (pullbackSectionsOnTensorMap g M V V' h) := by
  let _ : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
  have hτ := isIso_transpose_pullbackSectionsNative g M V hV V' hV' h
  have hb := ConcreteCategory.bijective_of_isIso
    (((ModuleCat.extendRestrictScalarsAdj (g.appLE V V' h).hom).homEquiv _ _).symm
      (pullbackSectionsNative g M V V' h))
  have key : ∀ t : TensorProduct Γ(X, V) Γ(Y, V') Γ(M, V),
      pullbackSectionsOnTensorMap g M V V' h t =
        (((ModuleCat.extendRestrictScalarsAdj (g.appLE V V' h).hom).homEquiv _ _).symm
          (pullbackSectionsNative g M V V' h)).hom t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul s m => rfl
    | add x y hx hy => rw [map_add, hx, hy]; exact (map_add _ x y).symm
  have hfun : ⇑(pullbackSectionsOnTensorMap g M V V' h) =
      ⇑(((ModuleCat.extendRestrictScalarsAdj (g.appLE V V' h).hom).homEquiv _ _).symm
          (pullbackSectionsNative g M V V' h)).hom := funext key
  rw [hfun]
  exact hb

end Scheme.Modules

section BaseChangeMain

variable {W Z C C' : Scheme.{u}} (g : W ⟶ Z) (p : Z ⟶ C) (q : W ⟶ C') (b : C' ⟶ C)

/-- **The affine computation for Stacks 01V0.** For a fibre-product square `IsPullback g q p b` and
affine opens `C₀ ⊆ C`, `Z₀ ⊆ p⁻¹C₀`, `C'₀ ⊆ b⁻¹C₀`, put `W₀ := g⁻¹Z₀ ⊓ q⁻¹C'₀` (affine, lemma 1).
Then `pullbackMap.app W₀ : Γ(W₀, g^*Ω_{Z/C}) → Γ(W₀, Ω_{W/C'})` is bijective.

Proof. Write `R = Γ(C₀)`, `S = Γ(C'₀)`, `A = Γ(Z₀)`, `B = Γ(W₀)`; `B = S ⊗_R A` (lemma 2). The
canonical map `Φ : B ⊗_A Γ(Ω_{Z/C}, Z₀) → Γ(W₀, g^*Ω_{Z/C})` is bijective (lemma 3), and
`Γ(Ω_{Z/C}, Z₀) ≅ Ω[A⁄R]`, `Γ(Ω_{W/C'}, W₀) ≅ Ω[B⁄S]` (`Omega_appIso`, Stacks 01UT), and
`B ⊗_A Ω[A⁄R] ≅ Ω[B⁄S]` (Mathlib `KaehlerDifferential.tensorKaehlerEquiv`, Stacks 00RV). The composite
isomorphism `E : B ⊗_A Γ(Ω_{Z/C}, Z₀) ≃ Γ(Ω_{W/C'}, W₀)` and `pullbackMap.app W₀ ∘ Φ` are both
`B`-linear and agree on the generators `1 ⊗ d a` (`a ∈ A`): both give `d (g^♯ a)` (lemma 4 on the
left; `tensorKaehlerEquiv_tmul_D` and `Omega_appIso_d` on the right). Since `Γ(Ω_{Z/C}, Z₀)` is
spanned over `A` by the `d a` (via `Omega_appIso` and `KaehlerDifferential.span_range_derivation`),
the two maps coincide, so `pullbackMap.app W₀ ∘ Φ` is bijective, hence so is `pullbackMap.app W₀`. -/
theorem Omega.pullbackMap_app_bijective_of_isPullback (h : IsPullback g q p b)
    {C₀ : C.Opens} {Z₀ : Z.Opens} {C'₀ : C'.Opens}
    (hC₀ : IsAffineOpen C₀) (hZ₀ : IsAffineOpen Z₀) (hC'₀ : IsAffineOpen C'₀)
    (hZ : Z₀ ≤ p ⁻¹ᵁ C₀) (hC' : C'₀ ≤ b ⁻¹ᵁ C₀) :
    Function.Bijective ((Omega.pullbackMap g p q b h.w).app (g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)).hom := by
  have hWZ : g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀ ≤ g ⁻¹ᵁ Z₀ := inf_le_left
  have hWC' : g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀ ≤ q ⁻¹ᵁ C'₀ := inf_le_right
  have hW₀ : IsAffineOpen (g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) :=
    Omega.isAffineOpen_inf_preimage_of_isPullback g p q b h hC₀ hZ₀ hC'₀ hZ hC'
  haveI := Omega_isQuasicoherent p
  let _ : Algebra Γ(C, C₀) Γ(Z, Z₀) := (p.appLE C₀ Z₀ hZ).hom.toAlgebra
  let _ : Algebra Γ(C, C₀) Γ(C', C'₀) := (b.appLE C₀ C'₀ hC').hom.toAlgebra
  let _ : Algebra Γ(Z, Z₀) Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) := (g.appLE Z₀ _ hWZ).hom.toAlgebra
  let _ : Algebra Γ(C', C'₀) Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) := (q.appLE C'₀ _ hWC').hom.toAlgebra
  let _ : Algebra Γ(C, C₀) Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) :=
    ((g ≫ p).appLE C₀ _ (hWZ.trans ((Opens.map g.base).map (homOfLE hZ)).le)).hom.toAlgebra
  have : IsScalarTower Γ(C, C₀) Γ(Z, Z₀) Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
      (Scheme.Hom.appLE_comp_appLE g p C₀ Z₀ _ hZ hWZ)).symm
  have : IsScalarTower Γ(C, C₀) Γ(C', C'₀) Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
      ((Scheme.Hom.appLE_comp_appLE q b C₀ C'₀ _ hC' hWC').trans
        (Omega.appLE_congr_hom h.w.symm C₀ _ _ _))).symm
  have : Algebra.IsPushout Γ(C, C₀) Γ(C', C'₀) Γ(Z, Z₀) Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) :=
    Omega.algebra_isPushout_of_isPullback g p q b h hC₀ hZ₀ hC'₀ hZ hC' rfl hWZ hWC' rfl rfl rfl rfl
  -- the maps
  let Φ := Scheme.Modules.pullbackSectionsOnTensorMap g (Omega p) Z₀ _ hWZ
  have hΦ : Function.Bijective Φ :=
    Scheme.Modules.pullbackSectionsOnTensorMap_bijective g (Omega p) Z₀ _ hWZ hZ₀ hW₀
  let eA := Omega_appIso p hC₀ hZ₀ hZ
  let eB := Omega_appIso q hC'₀ hW₀ hWC'
  let eT : TensorProduct Γ(Z, Z₀) Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) Γ(Omega p, Z₀) ≃ₗ[Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)]
      TensorProduct Γ(Z, Z₀) Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) Ω[Γ(Z, Z₀)⁄Γ(C, C₀)] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) eA
  let E := eT ≪≫ₗ KaehlerDifferential.tensorKaehlerEquiv Γ(C, C₀) Γ(C', C'₀) Γ(Z, Z₀)
    Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) ≪≫ₗ eB.symm
  let F₁ : TensorProduct Γ(Z, Z₀) Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) Γ(Omega p, Z₀) →ₗ[Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)]
      Γ(Omega q, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) :=
    { toFun := fun t => ((Omega.pullbackMap g p q b h.w).app _).hom (Φ t)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun c t => by
        simp only [map_smul, RingHom.id_apply]
        exact Scheme.Modules.Hom.app_smul (Omega.pullbackMap g p q b h.w) c (Φ t) }
  -- generators
  have gen : ∀ a : Γ(Z, Z₀),
      F₁ ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] (Omega.universalDerivation p).d (X := op Z₀) a) =
        E ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] (Omega.universalDerivation p).d (X := op Z₀) a) := by
    intro a
    have l1 : F₁ ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] (Omega.universalDerivation p).d (X := op Z₀) a) =
        (Omega.universalDerivation q).d (X := op (g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ((g.appLE Z₀ _ hWZ).hom a) := by
      have hΦ1 : Φ ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] (Omega.universalDerivation p).d (X := op Z₀) a) =
          Scheme.Modules.pullbackSectionsOn g (Omega p) Z₀ _ hWZ
            ((Omega.universalDerivation p).d (X := op Z₀) a) :=
        (Scheme.Modules.pullbackSectionsOnTensorMap_tmul g (Omega p) Z₀ _ hWZ 1 _).trans (one_smul _ _)
      show ((Omega.pullbackMap g p q b h.w).app _).hom (Φ (1 ⊗ₜ _)) = _
      rw [hΦ1]
      exact Omega.pullbackMap_app_pullbackSectionsOn_d g p q b h.w hWZ a
    have e1 : eT ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] (Omega.universalDerivation p).d (X := op Z₀) a) =
        (1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] KaehlerDifferential.D Γ(C, C₀) Γ(Z, Z₀) a := by
      have h1 : eT ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] (Omega.universalDerivation p).d (X := op Z₀) a) =
          (LinearEquiv.refl _ _) (1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)]
            eA ((Omega.universalDerivation p).d (X := op Z₀) a) :=
        TensorProduct.AlgebraTensorModule.congr_tmul _ _ _ _
      exact h1.trans (congrArg (fun x => (1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] x)
        (Omega_appIso_d p hC₀ hZ₀ hZ a))
    have r1 : E ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] (Omega.universalDerivation p).d (X := op Z₀) a) =
        (Omega.universalDerivation q).d (X := op (g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ((g.appLE Z₀ _ hWZ).hom a) := by
      show eB.symm (KaehlerDifferential.tensorKaehlerEquiv _ _ _ _ (eT (1 ⊗ₜ _))) = _
      rw [e1, KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul]
      apply eB.symm_apply_eq.mpr
      exact (Omega_appIso_d q hC'₀ hW₀ hWC' _).symm
    rw [l1, r1]
  -- all `1 ⊗ m`
  have key1 : ∀ m : Γ(Omega p, Z₀),
      F₁ ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] m) =
        E ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] m) := by
    intro m
    have hm : eA m ∈ Submodule.span Γ(Z, Z₀)
        (Set.range (KaehlerDifferential.D Γ(C, C₀) Γ(Z, Z₀))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    have h' : ∀ ω ∈ Submodule.span Γ(Z, Z₀) (Set.range (KaehlerDifferential.D Γ(C, C₀) Γ(Z, Z₀))),
        F₁ ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] eA.symm ω) =
          E ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] eA.symm ω) := by
      intro ω hω
      induction hω using Submodule.span_induction with
      | mem ω hω =>
        obtain ⟨a, rfl⟩ := hω
        have hda : eA.symm (KaehlerDifferential.D Γ(C, C₀) Γ(Z, Z₀) a) =
            (Omega.universalDerivation p).d (X := op Z₀) a :=
          eA.symm_apply_eq.mpr (Omega_appIso_d p hC₀ hZ₀ hZ a).symm
        rw [hda]
        exact gen a
      | zero => rw [map_zero, TensorProduct.tmul_zero, map_zero, map_zero]
      | add x y _ _ hx hy => rw [map_add, TensorProduct.tmul_add, map_add, map_add, hx, hy]
      | smul c x _ hx =>
        rw [map_smul, TensorProduct.tmul_smul, ← algebraMap_smul Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) c,
          map_smul, map_smul, hx]
    have := h' (eA m) hm
    rwa [eA.symm_apply_apply] at this
  have key : ∀ t, F₁ t = E t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s m =>
      have hs : (s ⊗ₜ[Γ(Z, Z₀)] m : TensorProduct Γ(Z, Z₀) Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀) Γ(Omega p, Z₀)) =
          s • ((1 : Γ(W, g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)) ⊗ₜ[Γ(Z, Z₀)] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, key1]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcomp : Function.Bijective
      (fun t => ((Omega.pullbackMap g p q b h.w).app _).hom (Φ t)) := by
    have : (fun t => ((Omega.pullbackMap g p q b h.w).app (g ⁻¹ᵁ Z₀ ⊓ q ⁻¹ᵁ C'₀)).hom (Φ t)) = ⇑E :=
      funext key
    rw [this]
    exact E.bijective
  exact (Function.Bijective.of_comp_iff _ hΦ).mp hcomp

end BaseChangeMain

end AlgebraicGeometry

/-- **Base change for relative differentials (Stacks 01V0).** If the commutative square
`g ≫ p = q ≫ b` (`g : W ⟶ Z`, `p : Z ⟶ C`, `q : W ⟶ C'`, `b : C' ⟶ C`) is a fibre-product square,
i.e. `W = Z ×_C C'`, then `pullbackMap : g^*Ω_{Z/C} ⟶ Ω_{W/C'}` is an isomorphism.

Source: Stacks 01V0 (Lemma 29.32.10 in the Morphisms chapter), whose proof reduces to the affine
statement Stacks 00RV / Mathlib `KaehlerDifferential.tensorKaehlerEquiv` (`B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S]`
for `B = S ⊗[R] A`, i.e. for `Algebra.IsPushout R S A B`).

Proof. Both sides are quasi-coherent (`Omega_isQuasicoherent`,
`isQuasicoherent_pullback`), so by `Scheme.Modules.isIso_of_affineOpens_cover_bijective`
(Stacks 01AI: isomorphisms are detected on stalks; 01I6: quasi-coherent modules on an affine scheme are
determined by global sections) it suffices to find affine opens covering `W` on which `pullbackMap.app`
is bijective. For `w ∈ W` choose affine `C₀ ∋ p (g w)`, affine `Z₀ ∋ g w` with `Z₀ ≤ p⁻¹C₀`, affine
`C'₀ ∋ q w` with `C'₀ ≤ b⁻¹C₀` (`isBasis_affineOpens`; `b (q w) = p (g w)` by the square), and put
`W₀ := g⁻¹Z₀ ⊓ q⁻¹C'₀ ∋ w`. Then:
* `W₀` is affine (`Omega.isAffineOpen_inf_preimage_of_isPullback`: the restricted square is a
  fibre-product square by Mathlib `Scheme.Hom.isPullback_resLE`, so `W₀ = Z₀ ×_{C₀} C'₀`);
* `Γ(W₀) = Γ(C'₀) ⊗_{Γ(C₀)} Γ(Z₀)` (`Omega.algebra_isPushout_of_isPullback`, from Mathlib
  `isIso_pushoutSection_of_isAffineOpen`, Stacks 01JQ);
* `pullbackMap.app W₀` is bijective (`Omega.pullbackMap_app_bijective_of_isPullback`): it is compared
  through `Γ(W₀) ⊗_{Γ(Z₀)} Γ(Ω_{Z/C}, Z₀) ≃ Γ(W₀, g^*Ω_{Z/C})` (Stacks 01I9,
  `pullbackSectionsOnTensorMap_bijective`), `Γ(Ω_{Z/C}, Z₀) ≃ Ω[Γ(Z₀)⁄Γ(C₀)]`,
  `Γ(Ω_{W/C'}, W₀) ≃ Ω[Γ(W₀)⁄Γ(C'₀)]` (`Omega_appIso`, Stacks 01UT) with Mathlib's
  `KaehlerDifferential.tensorKaehlerEquiv`; both maps are `Γ(W₀)`-linear and agree on the generators
  `1 ⊗ d a ↦ d (g^♯ a)` (`Omega.pullbackMap_app_pullbackSectionsOn_d`, `tensorKaehlerEquiv_tmul_D`,
  `Omega_appIso_d`).

Edge cases: empty `W` (both sides zero, trivially an isomorphism); `C = C'` and `b = 𝟙` (then `g` is an
isomorphism); rank 0 is not an issue since no local freeness is assumed. The statement needs no
smoothness, flatness or finiteness hypothesis (Stacks 01V0 has none). Used for the comparisons
`pr₁^*Ω_{A¹/k} ≅ Ω_{P/𝒵}` and `T_{(C×X)/C} ≅ pr₂^*T_X`; `Omega_baseChange` (a `Nonempty ≅`) follows
from this theorem by `⟨asIso _⟩`. -/
theorem AlgebraicGeometry.Omega.pullbackMap_isIso_of_isPullback {W Z C C' : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ Z) (p : Z ⟶ C) (q : W ⟶ C') (b : C' ⟶ C) (h : CategoryTheory.IsPullback g q p b) :
    CategoryTheory.IsIso (AlgebraicGeometry.Omega.pullbackMap g p q b h.w) := by
  haveI := AlgebraicGeometry.Omega_isQuasicoherent p
  haveI := AlgebraicGeometry.Omega_isQuasicoherent q
  let ι := {t : C.affineOpens × Z.affineOpens × C'.affineOpens //
    t.2.1.1 ≤ p ⁻¹ᵁ t.1.1 ∧ t.2.2.1 ≤ b ⁻¹ᵁ t.1.1}
  refine AlgebraicGeometry.Scheme.Modules.isIso_of_affineOpens_cover_bijective _
    (fun t : ι => g ⁻¹ᵁ t.1.2.1.1 ⊓ q ⁻¹ᵁ t.1.2.2.1) ?_ ?_ ?_
  · intro t
    exact AlgebraicGeometry.Omega.isAffineOpen_inf_preimage_of_isPullback g p q b h
      t.1.1.2 t.1.2.1.2 t.1.2.2.2 t.2.1 t.2.2
  · intro w
    obtain ⟨_, ⟨C₀, hC₀ : AlgebraicGeometry.IsAffineOpen C₀, rfl⟩, hw₀, -⟩ :=
      C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p (g w))) isOpen_univ
    obtain ⟨_, ⟨Z₀, hZ₀ : AlgebraicGeometry.IsAffineOpen Z₀, rfl⟩, hgw, hZ⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (show g w ∈ p ⁻¹ᵁ C₀ from hw₀) (p ⁻¹ᵁ C₀).isOpen
    have hbq : q w ∈ b ⁻¹ᵁ C₀ := by
      show b (q w) ∈ C₀
      have e : b (q w) = p (g w) := by
        have := congrArg (fun f : W ⟶ C => f w) h.w
        simpa using this.symm
      rw [e]; exact hw₀
    obtain ⟨_, ⟨C'₀, hC'₀ : AlgebraicGeometry.IsAffineOpen C'₀, rfl⟩, hqw, hC'⟩ :=
      C'.isBasis_affineOpens.exists_subset_of_mem_open hbq (b ⁻¹ᵁ C₀).isOpen
    exact ⟨⟨(⟨C₀, hC₀⟩, ⟨Z₀, hZ₀⟩, ⟨C'₀, hC'₀⟩), hZ, hC'⟩, hgw, hqw⟩
  · intro t
    exact AlgebraicGeometry.Omega.pullbackMap_app_bijective_of_isPullback g p q b h
      t.1.1.2 t.1.2.1.2 t.1.2.2.2 t.2.1 t.2.2

end
