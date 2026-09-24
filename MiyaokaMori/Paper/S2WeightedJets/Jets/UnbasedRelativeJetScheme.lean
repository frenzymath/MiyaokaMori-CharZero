import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetConstantTerm
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetFunctor
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme

/-! # The unbased relative jet scheme

The relative jet scheme `J_r(Z/S)` with unconstrained constant term (the relative version of the functor-of-points
definition of Ein–Mustață §2): the `T`-points of an `S`-scheme `T` are the `S`-morphisms
`T ×_k Spec k[t]/(t^{r+1}) → Z`. It comes with the constant-term projection `π_r : J_r(Z/S) → Z` and the
functoriality `J_r(g)` (§2 of the paper, `J_k(𝒵^×/C)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## The three proof obligations of `jetFunctor` -/

/-- The subtype condition of `jetFunctor.map`: pulling back a jet `γ` over `T` along `g : T' ⟶ T` gives a jet
over `T'`. Proof: `γ ≫ pZ = pr ≫ T.hom`, `jetThickeningMap_proj` (`(g × 𝟙) ≫ pr = pr ≫ g`) and `Over.w g`. -/

theorem jetFunctor_map_prop {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    (pZ : Z ⟶ S) (r : ℕ) {T T' : CategoryTheory.Over S}
    [T.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [T'.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : T' ⟶ T) [g.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (γ : jetThickening (k := k) r T.left ⟶ Z)
    (hγ : γ ≫ pZ = jetThickeningProj (k := k) r T.left ≫ T.hom) :
    (jetThickeningMap (k := k) r g.left ≫ γ) ≫ pZ =
      jetThickeningProj (k := k) r T'.left ≫ T'.hom := by
  rw [CategoryTheory.Category.assoc, hγ, ← CategoryTheory.Category.assoc,
    jetThickeningMap_proj, CategoryTheory.Category.assoc, CategoryTheory.Over.w]

/-- The content of `jetFunctor.map_id`: pulling back along `𝟙` does nothing (`jetThickeningMap_id`). -/

theorem jetFunctor_map_id {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    (r : ℕ) {T : CategoryTheory.Over S}
    [T.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (γ : jetThickening (k := k) r T.left ⟶ Z) :
    jetThickeningMap (k := k) r (CategoryTheory.CategoryStruct.id T.left) ≫ γ = γ := by
  rw [jetThickeningMap_id, CategoryTheory.Category.id_comp]

/-- The content of `jetFunctor.map_comp`: pulling back along a composite is the composite of the pullbacks
(`jetThickeningMap_comp`). -/

theorem jetFunctor_map_comp {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    (r : ℕ) {T T' T'' : CategoryTheory.Over S}
    [T.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [T'.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [T''.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : T' ⟶ T) (h : T'' ⟶ T')
    [g.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [h.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (γ : jetThickening (k := k) r T.left ⟶ Z) :
    jetThickeningMap (k := k) r (h.left ≫ g.left) ≫ γ =
      jetThickeningMap (k := k) r h.left ≫ jetThickeningMap (k := k) r g.left ≫ γ := by
  rw [jetThickeningMap_comp, CategoryTheory.Category.assoc]

/-- The functor of points: an `S`-scheme `T` is sent to `{γ : T ×_k D_r → Z // γ is over S}` (`T` is a `k`-scheme
via `T.hom ≫ (S → Spec k)`); precomposition with `jetThickeningMap` gives functoriality. -/

noncomputable def jetFunctor {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S) :
    (CategoryTheory.Over S)ᵒᵖ ⥤ Type u where
  obj T :=
    letI : T.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨T.unop.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    { γ : jetThickening (k := k) r T.unop.left ⟶ Z //
      γ ≫ pZ = jetThickeningProj (k := k) r T.unop.left ≫ T.unop.hom }
  map {T T'} g :=
    letI : T.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨T.unop.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : T'.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨T'.unop.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    haveI : g.unop.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨CategoryTheory.Over.w_assoc g.unop _⟩
    TypeCat.ofHom (fun γ => ⟨jetThickeningMap (k := k) r g.unop.left ≫ γ.1,
      jetFunctor_map_prop (k := k) pZ r g.unop γ.1 γ.2⟩)
  map_id T := by
    letI : T.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨T.unop.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    apply TypeCat.homEquiv.injective
    funext γ
    apply Subtype.ext
    show jetThickeningMap (k := k) r (CategoryTheory.CategoryStruct.id T.unop.left) ≫ γ.1 = γ.1
    exact jetFunctor_map_id (k := k) (Z := Z) r γ.1
  map_comp {T T' T''} g h := by
    letI : T.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨T.unop.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : T'.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨T'.unop.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : T''.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨T''.unop.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    haveI : g.unop.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨CategoryTheory.Over.w_assoc g.unop _⟩
    haveI : h.unop.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨CategoryTheory.Over.w_assoc h.unop _⟩
    apply TypeCat.homEquiv.injective
    funext γ
    apply Subtype.ext
    show jetThickeningMap (k := k) r (h.unop.left ≫ g.unop.left) ≫ γ.1 =
      jetThickeningMap (k := k) r h.unop.left ≫ jetThickeningMap (k := k) r g.unop.left ≫ γ.1
    exact jetFunctor_map_comp (k := k) (Z := Z) r g.unop h.unop γ.1

/- Construction (the diagonal trick, avoiding a choice of representing object): when `Z` is affine over `S`,
   `Z ×_S Z` is an affine scheme over `Z` via the first projection, and the diagonal `Δ` is a section of it.
   The based jets with constant term `Δ` (the glued construction `relativeJetScheme` with `C := Z`) are exactly
   the jets of `Z/S` with unconstrained constant term: a based jet `γ' : T ×_k D_r → Z ×_S Z` over `w : T → Z`
   goes to `γ' ≫ pr₂`, and conversely `γ ↦ (pr ≫ ι₀^*γ, γ)`. Thus `J_r(Z/S) := J_r^Δ((Z ×_S Z)/Z)`, and the
   constant-term map `proj` is its structure morphism to `Z`. -/

/-- The canonical isomorphism between the jet thickenings of one scheme with respect to two equal `k`-structure
morphisms (`pullback.congrHom`). -/

noncomputable def jetThickening.congrIso {k : Type u} [Field k] (r : ℕ) (T : AlgebraicGeometry.Scheme.{u})
    (a b : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (h : a = b) :
    @jetThickening k _ r T ⟨a⟩ ≅ @jetThickening k _ r T ⟨b⟩ :=
  CategoryTheory.Limits.pullback.congrHom h rfl

/-- The forward direction of `congrIso` is `pullback.map` with identity components; the proof arguments are
propositions, so this is `rfl`. -/

theorem jetThickening.congrIso_hom_eq_map {k : Type u} [Field k] (r : ℕ) (T : AlgebraicGeometry.Scheme.{u})
    (a b : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (h : a = b) :
    (jetThickening.congrIso (k := k) r T a b h).hom =
      CategoryTheory.Limits.pullback.map a (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        b (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (CategoryTheory.CategoryStruct.id T) (CategoryTheory.CategoryStruct.id (jetBase k r))
        (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of k)))
        (by simp [h]) (by simp) :=
  rfl

/-- `congrIso` is compatible with the projection to `T`: `congrIso.hom ≫ pr = pr`. -/

@[reassoc]
theorem jetThickening.congrIso_hom_proj {k : Type u} [Field k] (r : ℕ) (T : AlgebraicGeometry.Scheme.{u})
    (a b : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (h : a = b) :
    (jetThickening.congrIso (k := k) r T a b h).hom ≫ @jetThickeningProj k _ r T ⟨b⟩ =
      @jetThickeningProj k _ r T ⟨a⟩ := by
  rw [jetThickening.congrIso_hom_eq_map]
  show CategoryTheory.Limits.pullback.map _ _ _ _ _ _ _ _ _ ≫
    CategoryTheory.Limits.pullback.fst _ _ = CategoryTheory.Limits.pullback.fst _ _
  rw [CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Category.comp_id]

/-- `congrIso` is compatible with the constant-term section: `ι₀ ≫ congrIso.hom = ι₀`. -/

@[reassoc]
theorem jetThickening.congrIso_jetConstantTerm {k : Type u} [Field k] (r : ℕ)
    (T : AlgebraicGeometry.Scheme.{u})
    (a b : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (h : a = b) :
    @jetConstantTerm k _ r T ⟨a⟩ ≫ (jetThickening.congrIso (k := k) r T a b h).hom =
      @jetConstantTerm k _ r T ⟨b⟩ := by
  subst h
  rw [jetThickening.congrIso_hom_eq_map, CategoryTheory.Limits.pullback.map_id]
  exact CategoryTheory.Category.comp_id _

/-- `congrIso` at `a = a` is the identity (`pullback.map_id`; the proof argument is arbitrary by proof
irrelevance). -/

theorem jetThickening.congrIso_refl_hom {k : Type u} [Field k] (r : ℕ) (T : AlgebraicGeometry.Scheme.{u})
    (a : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (h : a = a) :
    (jetThickening.congrIso (k := k) r T a a h).hom =
      CategoryTheory.CategoryStruct.id (@jetThickening k _ r T ⟨a⟩) := by
  rw [jetThickening.congrIso_hom_eq_map]
  exact CategoryTheory.Limits.pullback.map_id

/-- Transitivity of `congrIso`: `congrIso(a,b).hom ≫ congrIso(b,c).hom = congrIso(a,c).hom` (after `subst` all
three are identities). -/

@[reassoc]
theorem jetThickening.congrIso_hom_trans {k : Type u} [Field k] (r : ℕ) (T : AlgebraicGeometry.Scheme.{u})
    (a b c : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (h : a = b) (h' : b = c) :
    (jetThickening.congrIso (k := k) r T a b h).hom ≫ (jetThickening.congrIso (k := k) r T b c h').hom =
      (jetThickening.congrIso (k := k) r T a c (h.trans h')).hom := by
  subst h h'
  simp only [jetThickening.congrIso_refl_hom, CategoryTheory.Category.id_comp]

/-- The forward direction of `congrIso` is `jetThickeningMap` along `𝟙 T` (with the two different `k`-structures
on source and target); `rfl`. -/

theorem jetThickening.congrIso_hom_eq_jetThickeningMap_id {k : Type u} [Field k] (r : ℕ)
    (T : AlgebraicGeometry.Scheme.{u})
    (a b : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (h : a = b) :
    (jetThickening.congrIso (k := k) r T a b h).hom =
      @jetThickeningMap k _ r T T ⟨a⟩ ⟨b⟩ (CategoryTheory.CategoryStruct.id T)
        (@CategoryTheory.HomIsOver.mk _ _ T T (CategoryTheory.CategoryStruct.id T)
          (AlgebraicGeometry.Spec (CommRingCat.of k)) ⟨a⟩ ⟨b⟩
          ((CategoryTheory.Category.id_comp b).trans h.symm)) :=
  rfl

/-- `congrIso` commutes with `jetThickeningMap`: the maps `(g × 𝟙)` for the two `k`-structures agree after
aligning by `congrIso` (after `subst` both `congrIso` are identities and the two `jetThickeningMap` differ only
in `Prop` instances). -/

@[reassoc]
theorem jetThickening.congrIso_hom_jetThickeningMap {k : Type u} [Field k] (r : ℕ)
    {W W' : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ W')
    (a a' : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (b b' : W' ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (ha : a = a') (hb : b = b')
    (inst : @AlgebraicGeometry.Scheme.Hom.IsOver W W' g (AlgebraicGeometry.Spec (CommRingCat.of k)) ⟨a⟩ ⟨b⟩)
    (inst' : @AlgebraicGeometry.Scheme.Hom.IsOver W W' g (AlgebraicGeometry.Spec (CommRingCat.of k)) ⟨a'⟩ ⟨b'⟩) :
    (jetThickening.congrIso (k := k) r W a a' ha).hom ≫ @jetThickeningMap k _ r W W' ⟨a'⟩ ⟨b'⟩ g inst' =
      @jetThickeningMap k _ r W W' ⟨a⟩ ⟨b⟩ g inst ≫ (jetThickening.congrIso (k := k) r W' b b' hb).hom := by
  subst ha hb
  rw [jetThickening.congrIso_refl_hom, jetThickening.congrIso_refl_hom,
    CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id]

/- `Z` affine over `S` implies that the first projection `Z ×_S Z → Z` is affine (affine morphisms are stable
   under base change, Mathlib). -/

set_option backward.isDefEq.respectTransparency.types false in

theorem jetScheme.isAffineHom_fst {S Z : AlgebraicGeometry.Scheme.{u}} (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ] :
    AlgebraicGeometry.IsAffineHom (CategoryTheory.Limits.pullback.fst pZ pZ) :=
  CategoryTheory.MorphismProperty.pullback_fst (P := @AlgebraicGeometry.IsAffineHom) _ _ ‹_›

/-- The based jet scheme (in `Over Z`) of `Z ×_S Z`, viewed as a scheme over `Z` via the first projection, with
the diagonal as the section. -/

noncomputable def jetScheme.diagonalJet {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ] : CategoryTheory.Over Z :=
  letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : AlgebraicGeometry.IsAffineHom (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
    jetScheme.isAffineHom_fst pZ
  relativeJetScheme (k := k) (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ))
    (CategoryTheory.Limits.pullback.diagonal pZ) (CategoryTheory.Limits.pullback.diagonal_fst pZ) r

/-- `J_r(Z/S)` for `Z` affine over `S`: the underlying scheme of the diagonal based jet scheme. -/

noncomputable def jetScheme {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ] : AlgebraicGeometry.Scheme.{u} :=
  (jetScheme.diagonalJet (k := k) r pZ).left

/-- `π_r`, taking the constant term: the structure morphism of the diagonal based jet scheme to `Z`. -/

noncomputable def jetScheme.proj {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ] : jetScheme (k := k) r pZ ⟶ Z :=
  (jetScheme.diagonalJet (k := k) r pZ).hom

/-! ## The proof obligations of `jetScheme.homEquiv` -/

section HomEquivObligations

variable {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
  [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  (pZ : Z ⟶ S) (r : ℕ) (T : AlgebraicGeometry.Scheme.{u}) (t : T ⟶ S)

/-- The equality hypothesis for `congrIso`: a constant term `w` over `t` (i.e. `w ≫ pZ = t`) gives the same
`k`-structure morphism. -/

theorem jetScheme.homEquiv_over (w : T ⟶ Z) (hw : w ≫ pZ = t) :
    t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  rw [← hw, CategoryTheory.Category.assoc]

/-- The subtype condition of `homEquiv.toFun`: `γ' ≫ pr₂` lies over `t`. Uses `pullback.condition`
(`pr₂ ≫ pZ = pr₁ ≫ pZ`), the first condition of a based jet and `congrIso_hom_proj`. -/

theorem jetScheme.homEquiv_toFun_prop (w : T ⟶ Z) (hw : w ≫ pZ = t)
    (h : t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (φ : @jetThickening k _ r T ⟨w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ⟶
      CategoryTheory.Limits.pullback pZ pZ)
    (hφ : φ ≫ CategoryTheory.Limits.pullback.fst pZ pZ =
      @jetThickeningProj k _ r T ⟨w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ w) :
    ((jetThickening.congrIso (k := k) r T _ _ h).hom ≫ φ ≫
        CategoryTheory.Limits.pullback.snd pZ pZ) ≫ pZ =
      @jetThickeningProj k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ t := by
  have key : φ ≫ CategoryTheory.Limits.pullback.snd pZ pZ ≫ pZ =
      @jetThickeningProj k _ r T ⟨w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫
        (w ≫ pZ) := by
    rw [← CategoryTheory.Limits.pullback.condition, ← CategoryTheory.Category.assoc φ, hφ,
      CategoryTheory.Category.assoc]
  simp only [CategoryTheory.Category.assoc]
  rw [key, jetThickening.congrIso_hom_proj_assoc, hw]

/-- The constant term of `homEquiv.toFun`: `ι₀^*(γ' ≫ pr₂) = w` (`congrIso_jetConstantTerm`, the second
condition of a based jet, and `diagonal_snd`). -/

theorem jetScheme.homEquiv_toFun_constantTerm (w : T ⟶ Z)
    (h : t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (φ : @jetThickening k _ r T ⟨w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ⟶
      CategoryTheory.Limits.pullback pZ pZ)
    (hφ : @jetConstantTerm k _ r T ⟨w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ φ =
      w ≫ CategoryTheory.Limits.pullback.diagonal pZ) :
    @jetConstantTerm k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫
        ((jetThickening.congrIso (k := k) r T _ _ h).hom ≫ φ ≫
          CategoryTheory.Limits.pullback.snd pZ pZ) = w := by
  rw [jetThickening.congrIso_jetConstantTerm_assoc, reassoc_of% hφ,
    CategoryTheory.Limits.pullback.diagonal_snd, CategoryTheory.Category.comp_id]

/-- In `homEquiv.invFun`, `w := ι₀^*γ` lies over `t`: `ι₀ ≫ pr = 𝟙`. -/

theorem jetScheme.homEquiv_invFun_base
    (γ : @jetThickening k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ⟶ Z)
    (hγ : γ ≫ pZ =
      @jetThickeningProj k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ t) :
    (@jetConstantTerm k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ γ) ≫ pZ = t := by
  rw [CategoryTheory.Category.assoc, hγ, ← CategoryTheory.Category.assoc,
    jetConstantTerm_comp_proj, CategoryTheory.Category.id_comp]

/-- The compatibility condition for `pullback.lift` in `homEquiv.invFun`: `(pr ≫ w) ≫ pZ = γ ≫ pZ`. -/

theorem jetScheme.homEquiv_invFun_lift_cond
    (γ : @jetThickening k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ⟶ Z)
    (hγ : γ ≫ pZ =
      @jetThickeningProj k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ t)
    (w : T ⟶ Z) (hw : w ≫ pZ = t) :
    (@jetThickeningProj k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ w) ≫ pZ =
      γ ≫ pZ := by
  rw [hγ, CategoryTheory.Category.assoc, hw]

/-- The pair `(pr ≫ w, γ)` built in `homEquiv.invFun` is a based jet with constant term `w` (the two conditions
of `relativeJetFunctor`). -/

theorem jetScheme.homEquiv_invFun_basedJet
    (γ : @jetThickening k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ⟶ Z)
    (w : T ⟶ Z)
    (hw0 : @jetConstantTerm k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ γ = w)
    (h : w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hlift : (@jetThickeningProj k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ w) ≫ pZ =
      γ ≫ pZ) :
    ((jetThickening.congrIso (k := k) r T _ _ h).hom ≫
          CategoryTheory.Limits.pullback.lift
            (@jetThickeningProj k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ w)
            γ hlift) ≫ CategoryTheory.Limits.pullback.fst pZ pZ =
        @jetThickeningProj k _ r T ⟨w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ w ∧
      @jetConstantTerm k _ r T ⟨w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫
          ((jetThickening.congrIso (k := k) r T _ _ h).hom ≫
            CategoryTheory.Limits.pullback.lift
              (@jetThickeningProj k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ w)
              γ hlift) =
        w ≫ CategoryTheory.Limits.pullback.diagonal pZ := by
  constructor
  · simp only [CategoryTheory.Category.assoc]
    rw [CategoryTheory.Limits.pullback.lift_fst, jetThickening.congrIso_hom_proj_assoc]
  · apply CategoryTheory.Limits.pullback.hom_ext
    · simp only [CategoryTheory.Category.assoc]
      rw [CategoryTheory.Limits.pullback.lift_fst, jetThickening.congrIso_jetConstantTerm_assoc,
        jetConstantTerm_comp_proj_assoc, CategoryTheory.Limits.pullback.diagonal_fst,
        CategoryTheory.Category.comp_id]
    · simp only [CategoryTheory.Category.assoc]
      rw [CategoryTheory.Limits.pullback.lift_snd, jetThickening.congrIso_jetConstantTerm_assoc,
        hw0, CategoryTheory.Limits.pullback.diagonal_snd, CategoryTheory.Category.comp_id]

/-- The subtype condition of `homEquiv.invFun`: the resulting `T`-point lies over `t` (`Over.w`). -/

theorem jetScheme.homEquiv_invFun_prop [AlgebraicGeometry.IsAffineHom pZ]
    (w : T ⟶ Z) (hw : w ≫ pZ = t)
    (u : CategoryTheory.Over.mk w ⟶ jetScheme.diagonalJet (k := k) r pZ) :
    u.left ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t := by
  have hu : u.left ≫ jetScheme.proj (k := k) r pZ = w := CategoryTheory.Over.w u
  calc u.left ≫ jetScheme.proj (k := k) r pZ ≫ pZ
      = (u.left ≫ jetScheme.proj (k := k) r pZ) ≫ pZ := (CategoryTheory.Category.assoc _ _ _).symm
    _ = w ≫ pZ := by rw [hu]
    _ = t := hw

end HomEquivObligations

/-- The forward direction of `homEquiv`: `a ↦ w := a ≫ π_r`, then the pullback `γ'` of the universal based jet
along `a` composed with `pr₂`; the `k`-structures are aligned by `jetThickening.congrIso`. The subtype condition
is `jetScheme.homEquiv_toFun_prop`. -/

noncomputable def jetScheme.homEquivToFun {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ]
    (T : AlgebraicGeometry.Scheme.{u}) (t : T ⟶ S) :
    letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    { a : T ⟶ jetScheme (k := k) r pZ // a ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t } →
      { γ : jetThickening (k := k) r T ⟶ Z // γ ≫ pZ = jetThickeningProj (k := k) r T ≫ t } :=
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : AlgebraicGeometry.IsAffineHom (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
    jetScheme.isAffineHom_fst pZ
  fun a =>
    let w : T ⟶ Z := a.1 ≫ jetScheme.proj (k := k) r pZ
    have hw : w ≫ pZ = t := (CategoryTheory.Category.assoc _ _ _).trans a.2
    let γ' := (relativeJetScheme.representableBy (k := k)
        (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ))
        (CategoryTheory.Limits.pullback.diagonal pZ)
        (CategoryTheory.Limits.pullback.diagonal_fst pZ) r).homEquiv
      (X := CategoryTheory.Over.mk w)
      (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk w)
        (V := jetScheme.diagonalJet (k := k) r pZ) a.1 rfl)
    ⟨(jetThickening.congrIso (k := k) r T (t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
        (w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
        (jetScheme.homEquiv_over (k := k) pZ T t w hw)).hom ≫
      γ'.1 ≫ CategoryTheory.Limits.pullback.snd pZ pZ,
      jetScheme.homEquiv_toFun_prop (k := k) pZ r T t w hw
        (jetScheme.homEquiv_over (k := k) pZ T t w hw) γ'.1 γ'.2.1⟩

/-- The inverse direction of `homEquiv`: `γ ↦ w := ι₀^*γ`, the based jet `(pr ≫ w, γ) : T ×_k D_r → Z ×_S Z`,
then the inverse of `relativeJetScheme.representableBy` gives a morphism in `Over Z`, of which we take the
underlying morphism. -/

noncomputable def jetScheme.homEquivInvFun {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ]
    (T : AlgebraicGeometry.Scheme.{u}) (t : T ⟶ S) :
    letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    { γ : jetThickening (k := k) r T ⟶ Z // γ ≫ pZ = jetThickeningProj (k := k) r T ≫ t } →
      { a : T ⟶ jetScheme (k := k) r pZ // a ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t } :=
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : AlgebraicGeometry.IsAffineHom (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
    jetScheme.isAffineHom_fst pZ
  fun γ =>
    let w : T ⟶ Z := jetConstantTerm (k := k) r T ≫ γ.1
    have hw : w ≫ pZ = t := jetScheme.homEquiv_invFun_base (k := k) pZ r T t γ.1 γ.2
    have hover : w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      (jetScheme.homEquiv_over (k := k) pZ T t w hw).symm
    have hlift : (jetThickeningProj (k := k) r T ≫ w) ≫ pZ = γ.1 ≫ pZ :=
      jetScheme.homEquiv_invFun_lift_cond (k := k) pZ r T t γ.1 γ.2 w hw
    let u := ((relativeJetScheme.representableBy (k := k)
        (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ))
        (CategoryTheory.Limits.pullback.diagonal pZ)
        (CategoryTheory.Limits.pullback.diagonal_fst pZ) r).homEquiv
      (X := CategoryTheory.Over.mk w)).symm
      ⟨(jetThickening.congrIso (k := k) r T
            (w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
            (t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) hover).hom ≫
          CategoryTheory.Limits.pullback.lift (jetThickeningProj (k := k) r T ≫ w) γ.1 hlift,
        jetScheme.homEquiv_invFun_basedJet (k := k) pZ r T t γ.1 w rfl hover hlift⟩
    ⟨u.left, jetScheme.homEquiv_invFun_prop (k := k) pZ r T t w hw u⟩

section HomEquivInverse

variable {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
  [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  (r : ℕ) (pZ : Z ⟶ S) [AlgebraicGeometry.IsAffineHom pZ]
  (T : AlgebraicGeometry.Scheme.{u}) (t : T ⟶ S)

/-- The value of `homEquivToFun`, expressed through any morphism `u : Over.mk w ⟶ diagonalJet` in `Over Z`
representing `a` (`u.left = a`): `(toFun a).1 = congrIso.hom ≫ (e.homEquiv u).1 ≫ pr₂`. The definition uses
`w = a ≫ π_r` and `u = Over.homMk a rfl`; after `subst w` the two agree by `Over.OverMorphism.ext`. -/

theorem jetScheme.homEquivToFun_val
    (a : { a : T ⟶ jetScheme (k := k) r pZ // a ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t })
    (w : T ⟶ Z) (hw : w ≫ pZ = t)
    (u : CategoryTheory.Over.mk w ⟶ jetScheme.diagonalJet (k := k) r pZ) (hu : u.left = a.1) :
    letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    haveI : AlgebraicGeometry.IsAffineHom
        (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
      jetScheme.isAffineHom_fst pZ
    (jetScheme.homEquivToFun (k := k) r pZ T t a).1 =
      (jetThickening.congrIso (k := k) r T (t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
          (w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
          (jetScheme.homEquiv_over (k := k) pZ T t w hw)).hom ≫
        ((relativeJetScheme.representableBy (k := k)
            (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ))
            (CategoryTheory.Limits.pullback.diagonal pZ)
            (CategoryTheory.Limits.pullback.diagonal_fst pZ) r).homEquiv
          (X := CategoryTheory.Over.mk w) u).1 ≫ CategoryTheory.Limits.pullback.snd pZ pZ := by
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
    jetScheme.isAffineHom_fst pZ
  obtain ⟨a₁, ha₁⟩ := a
  dsimp only at hu
  have hw' : a₁ ≫ jetScheme.proj (k := k) r pZ = w := by
    rw [← hu]; exact CategoryTheory.Over.w u
  subst hw'
  have hu' : CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (a₁ ≫ jetScheme.proj (k := k) r pZ))
      (V := jetScheme.diagonalJet (k := k) r pZ) a₁ rfl = u := by
    apply CategoryTheory.Over.OverMorphism.ext
    exact hu.symm
  subst hu'
  rfl

/-- The value of `homEquivInvFun`: if `γ` is the jet `congrIso.hom ≫ (e.homEquiv u).1 ≫ pr₂` built from
`u : Over.mk w ⟶ diagonalJet`, then `(invFun γ).1 = u.left`.

Proof: the constant term `w₂ := ι₀ ≫ γ` recomputed in `invFun` equals `w` (`homEquiv_toFun_constantTerm`).
Let `f : Over.mk w₂ ⟶ Over.mk w` be the morphism with underlying map `𝟙 T`. By `Equiv.symm_apply_eq` it suffices
that the based jet built in `invFun` equals `e.homEquiv (f ≫ u) = F.map f (e.homEquiv u)` (`e.homEquiv_comp`)
`= jetThickeningMap 𝟙 ≫ (e.homEquiv u).1 = congrIso(w₂,w).hom ≫ (e.homEquiv u).1`; by `pullback.hom_ext`, in the
`pr₁` direction both sides are `pr ≫ w₂ = pr ≫ w`, and in the `pr₂` direction use `congrIso_hom_trans`. -/

theorem jetScheme.homEquivInvFun_val
    (γ : { γ : @jetThickening k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ⟶ Z //
      γ ≫ pZ = @jetThickeningProj k _ r T ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ t })
    (w : T ⟶ Z) (hw : w ≫ pZ = t)
    (u : CategoryTheory.Over.mk w ⟶ jetScheme.diagonalJet (k := k) r pZ)
    (hγ :
      letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
        ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
      haveI : AlgebraicGeometry.IsAffineHom
          (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
        jetScheme.isAffineHom_fst pZ
      γ.1 =
        (jetThickening.congrIso (k := k) r T (t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
            (w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
            (jetScheme.homEquiv_over (k := k) pZ T t w hw)).hom ≫
          ((relativeJetScheme.representableBy (k := k)
              (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ))
              (CategoryTheory.Limits.pullback.diagonal pZ)
              (CategoryTheory.Limits.pullback.diagonal_fst pZ) r).homEquiv
            (X := CategoryTheory.Over.mk w) u).1 ≫ CategoryTheory.Limits.pullback.snd pZ pZ) :
    (jetScheme.homEquivInvFun (k := k) r pZ T t γ).1 = u.left := by
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
    jetScheme.isAffineHom_fst pZ
  set e := relativeJetScheme.representableBy (k := k)
    (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ))
    (CategoryTheory.Limits.pullback.diagonal pZ)
    (CategoryTheory.Limits.pullback.diagonal_fst pZ) r with he
  obtain ⟨γv, hγv⟩ := γ
  dsimp only at hγ
  subst hγ
  -- `ψ` := the pullback of the universal based jet along `u`, with a clean type
  set ψ : @jetThickening k _ r T ⟨w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ⟶
      CategoryTheory.Limits.pullback pZ pZ := (e.homEquiv (X := CategoryTheory.Over.mk w) u).1 with hψ
  have hψ1 : ψ ≫ CategoryTheory.Limits.pullback.fst pZ pZ =
      @jetThickeningProj k _ r T ⟨w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ w :=
    (e.homEquiv u).2.1
  have hψ0 : @jetConstantTerm k _ r T ⟨w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫ ψ =
      w ≫ CategoryTheory.Limits.pullback.diagonal pZ :=
    (e.homEquiv u).2.2
  -- the constant term `w₂ = w`
  have hw₂ : jetConstantTerm (k := k) r T ≫
      ((jetThickening.congrIso (k := k) r T _ _ (jetScheme.homEquiv_over (k := k) pZ T t w hw)).hom ≫
        ψ ≫ CategoryTheory.Limits.pullback.snd pZ pZ) = w :=
    jetScheme.homEquiv_toFun_constantTerm (k := k) pZ r T t w _ ψ hψ0
  set γv := (jetThickening.congrIso (k := k) r T _ _ (jetScheme.homEquiv_over (k := k) pZ T t w hw)).hom ≫
        ψ ≫ CategoryTheory.Limits.pullback.snd pZ pZ with hγvdef
  have hstruct : (jetConstantTerm (k := k) r T ≫ γv) ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      w ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by rw [hw₂]
  -- `f : Over.mk w₂ ⟶ Over.mk w` with underlying map `𝟙 T`
  let f : CategoryTheory.Over.mk (jetConstantTerm (k := k) r T ≫ γv) ⟶ CategoryTheory.Over.mk w :=
    CategoryTheory.Over.homMk (CategoryTheory.CategoryStruct.id T)
      (by show CategoryTheory.CategoryStruct.id T ≫ w = jetConstantTerm (k := k) r T ≫ γv
          rw [CategoryTheory.Category.id_comp, hw₂])
  -- general form: any based jet equal to `congrIso.hom ≫ ψ` has underlying morphism `u.left` under `e.homEquiv.symm`
  have gen : ∀ φ : (relativeJetFunctor (k := k)
        (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ))
        (CategoryTheory.Limits.pullback.diagonal pZ)
        (CategoryTheory.Limits.pullback.diagonal_fst pZ) r).obj
          (Opposite.op (CategoryTheory.Over.mk (jetConstantTerm (k := k) r T ≫ γv))),
      φ.1 = (jetThickening.congrIso (k := k) r T _ _ hstruct).hom ≫ ψ →
      ((e.homEquiv (X := CategoryTheory.Over.mk (jetConstantTerm (k := k) r T ≫ γv))).symm φ).left = u.left := by
    intro φ hφ
    have hφu : (e.homEquiv (X := CategoryTheory.Over.mk (jetConstantTerm (k := k) r T ≫ γv))).symm φ = f ≫ u := by
      refine (Equiv.symm_apply_eq _).mpr ?_
      refine Eq.trans ?_ (e.homEquiv_comp f u).symm
      apply Subtype.ext
      rw [hφ]
      rfl
    rw [hφu]
    exact CategoryTheory.Category.id_comp _
  refine gen _ ?_
  show (jetThickening.congrIso (k := k) r T _ _ _).hom ≫
      CategoryTheory.Limits.pullback.lift
        (jetThickeningProj (k := k) r T ≫ (jetConstantTerm (k := k) r T ≫ γv)) γv _ =
      (jetThickening.congrIso (k := k) r T _ _ hstruct).hom ≫ ψ
  apply CategoryTheory.Limits.pullback.hom_ext
  · rw [CategoryTheory.Category.assoc _ ψ, hψ1,
      CategoryTheory.Category.assoc _ (CategoryTheory.Limits.pullback.lift _ _ _),
      CategoryTheory.Limits.pullback.lift_fst, jetThickening.congrIso_hom_proj_assoc,
      jetThickening.congrIso_hom_proj_assoc, hw₂]
  · rw [CategoryTheory.Category.assoc _ ψ,
      CategoryTheory.Category.assoc _ (CategoryTheory.Limits.pullback.lift _ _ _),
      CategoryTheory.Limits.pullback.lift_snd]
    refine (congrArg (fun x => (jetThickening.congrIso (k := k) r T _ _ _).hom ≫ x) hγvdef).trans ?_
    rw [jetThickening.congrIso_hom_trans_assoc]

end HomEquivInverse


/-- One half of the inverse laws of `homEquiv`: building the jet of a `T`-point and going back gives the original
`T`-point.

Proof (relative version of Ein–Mustață Prop. 2.2; uses only the `Equiv` structure of
`relativeJetScheme.representableBy` and its naturality `homEquiv_comp`): by definition
`(toFun a).1 = congrIso.hom ≫ (e.homEquiv (Over.homMk a.1 rfl)).1 ≫ pr₂`, so `jetScheme.homEquivInvFun_val` (with
`w := a ≫ π_r`, `u := Over.homMk a.1 rfl`, `hγ := rfl`) gives `(invFun (toFun a)).1 = (Over.homMk a.1 rfl).left = a.1`;
conclude with `Subtype.ext`. -/

theorem jetScheme.homEquiv_left_inv {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ]
    (T : AlgebraicGeometry.Scheme.{u}) (t : T ⟶ S) :
    letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    Function.LeftInverse (jetScheme.homEquivInvFun (k := k) r pZ T t)
      (jetScheme.homEquivToFun (k := k) r pZ T t) := by
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
    jetScheme.isAffineHom_fst pZ
  intro a
  apply Subtype.ext
  exact jetScheme.homEquivInvFun_val (k := k) r pZ T t (jetScheme.homEquivToFun (k := k) r pZ T t a)
    (a.1 ≫ jetScheme.proj (k := k) r pZ) ((CategoryTheory.Category.assoc _ _ _).trans a.2)
    (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (a.1 ≫ jetScheme.proj (k := k) r pZ))
      (V := jetScheme.diagonalJet (k := k) r pZ) a.1 rfl) rfl

/-- The other half of the inverse laws of `homEquiv`: building the `T`-point of a jet and going back gives the
original jet.

Proof (relative version of Ein–Mustață Prop. 2.2): `w := ι₀ ≫ γ`, and
`u := e.homEquiv.symm ⟨congrIso.hom ≫ pullback.lift (pr ≫ w) γ, …⟩` is the morphism in `Over Z` built in `invFun`,
with `(invFun γ).1 = u.left`. `jetScheme.homEquivToFun_val` (with `u` representing `invFun γ`, `hu := rfl`) gives
`(toFun (invFun γ)).1 = congrIso(t,w).hom ≫ (e.homEquiv (e.homEquiv.symm ⟨…⟩)).1 ≫ pr₂`; after
`Equiv.apply_symm_apply` this is `congrIso(t,w).hom ≫ (congrIso(w,t).hom ≫ pullback.lift (pr ≫ w) γ _) ≫ pr₂`,
which reduces to `γ` by `pullback.lift_snd`, `jetThickening.congrIso_hom_trans` and
`jetThickening.congrIso_refl_hom`. -/

theorem jetScheme.homEquiv_right_inv {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ]
    (T : AlgebraicGeometry.Scheme.{u}) (t : T ⟶ S) :
    letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    Function.RightInverse (jetScheme.homEquivInvFun (k := k) r pZ T t)
      (jetScheme.homEquivToFun (k := k) r pZ T t) := by
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
    jetScheme.isAffineHom_fst pZ
  intro γ
  apply Subtype.ext
  have hw : (jetConstantTerm (k := k) r T ≫ γ.1) ≫ pZ = t :=
    jetScheme.homEquiv_invFun_base (k := k) pZ r T t γ.1 γ.2
  rw [jetScheme.homEquivToFun_val (k := k) r pZ T t (jetScheme.homEquivInvFun (k := k) r pZ T t γ)
    (jetConstantTerm (k := k) r T ≫ γ.1) hw _ rfl]
  erw [Equiv.apply_symm_apply]
  show (jetThickening.congrIso (k := k) r T _ _ _).hom ≫
      ((jetThickening.congrIso (k := k) r T _ _ _).hom ≫
        CategoryTheory.Limits.pullback.lift
          (jetThickeningProj (k := k) r T ≫ (jetConstantTerm (k := k) r T ≫ γ.1)) γ.1 _) ≫
      CategoryTheory.Limits.pullback.snd pZ pZ = γ.1
  rw [CategoryTheory.Category.assoc _ (CategoryTheory.Limits.pullback.lift _ _ _),
    CategoryTheory.Limits.pullback.lift_snd, jetThickening.congrIso_hom_trans_assoc,
    jetThickening.congrIso_refl_hom, CategoryTheory.Category.id_comp]

/-- The functor of points: `T`-points over `t : T ⟶ S` correspond to `S`-morphisms `T ×_k D_r → Z`, and `proj`
corresponds to taking the constant term. Both directions go through `relativeJetScheme.representableBy`:
(→) `jetScheme.homEquivToFun`, (←) `jetScheme.homEquivInvFun`; the commutation conditions are the named theorems
above and the inverse laws are `jetScheme.homEquiv_left_inv` / `_right_inv`. -/

noncomputable def jetScheme.homEquiv {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ]
    (T : AlgebraicGeometry.Scheme.{u}) (t : T ⟶ S) :
    letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    { a : T ⟶ jetScheme (k := k) r pZ // a ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t } ≃
      { γ : jetThickening (k := k) r T ⟶ Z // γ ≫ pZ = jetThickeningProj (k := k) r T ≫ t } :=
  { toFun := jetScheme.homEquivToFun (k := k) r pZ T t
    invFun := jetScheme.homEquivInvFun (k := k) r pZ T t
    left_inv := jetScheme.homEquiv_left_inv (k := k) r pZ T t
    right_inv := jetScheme.homEquiv_right_inv (k := k) r pZ T t }

/-- In the category of `S`-schemes, "`T`-points over `g`" are the morphisms `T ⟶ Over.mk g` of `Over S` (pure
category theory). -/

def CategoryTheory.Over.homEquivSubtypeOverMk {S J : AlgebraicGeometry.Scheme.{u}} (g : J ⟶ S)
    (T : CategoryTheory.Over S) :
    (T ⟶ CategoryTheory.Over.mk g) ≃ { a : T.left ⟶ J // a ≫ g = T.hom } where
  toFun u := ⟨u.left, CategoryTheory.Over.w u⟩
  invFun a := CategoryTheory.Over.homMk a.1 a.2
  left_inv _ := by
    apply CategoryTheory.Over.OverMorphism.ext
    rfl
  right_inv _ := rfl

/-- Naturality of `jetScheme.homEquiv` (the `homEquiv_comp` field of `Functor.RepresentableBy`): precomposing a
`T`-point with `f : T' ⟶ T` corresponds to precomposing the jet with `jetThickeningMap f`.

Source: Ein–Mustață Prop. 2.2 (relative version); this transports the `homEquiv_comp` of
`relativeJetScheme.representableBy` through the two wrappers "take the constant term / build the based jet".

Proof: `w := a ≫ π_r`, `u₀ := Over.homMk a.1 rfl : Over.mk w ⟶ diagonalJet`,
`g := Over.homMk f.left : Over.mk (f.left ≫ w) ⟶ Over.mk w` (in `Over Z`). By `jetScheme.homEquivToFun_val`
(with `u := g ≫ u₀`, `hu := rfl`) the left side is `congrIso.hom ≫ (e.homEquiv (g ≫ u₀)).1 ≫ pr₂`, which
`e.homEquiv_comp g u₀` turns into `congrIso.hom ≫ jetThickeningMap f.left ≫ (e.homEquiv u₀).1 ≫ pr₂` (the `map`
of `relativeJetFunctor` is `jetThickeningMap ≫ ·` by definition); the right side is by definition
`jetThickeningMap f.left ≫ congrIso.hom ≫ (e.homEquiv u₀).1 ≫ pr₂`; the two agree by
`jetThickening.congrIso_hom_jetThickeningMap`.
Technical points: `rw [Category.assoc]` bites into the `k`-structure argument of `congrIso` (motive error), so
use the explicitly instantiated `Category.assoc _ ψ` and the `@[reassoc]` forms; `diagonalJet` and
`relativeJetScheme` are only definitionally equal, which `rw` does not see through at instance transparency, so
use `show` / term-mode `Eq.trans` there. -/

theorem jetScheme.homEquiv_comp {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ] {T T' : CategoryTheory.Over S} (f : T' ⟶ T)
    (a : { a : T.left ⟶ jetScheme (k := k) r pZ //
      a ≫ jetScheme.proj (k := k) r pZ ≫ pZ = T.hom }) :
    letI : T.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : T'.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨T'.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    haveI : f.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨CategoryTheory.Over.w_assoc f _⟩
    (jetScheme.homEquiv (k := k) r pZ T'.left T'.hom
        ⟨f.left ≫ a.1, by
          rw [CategoryTheory.Category.assoc, a.2]; exact CategoryTheory.Over.w f⟩).1 =
      jetThickeningMap (k := k) r f.left ≫
        (jetScheme.homEquiv (k := k) r pZ T.left T.hom a).1 := by
  letI : T.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : T'.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨T'.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : f.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc f _⟩
  letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
    jetScheme.isAffineHom_fst pZ
  set e := relativeJetScheme.representableBy (k := k)
    (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ))
    (CategoryTheory.Limits.pullback.diagonal pZ)
    (CategoryTheory.Limits.pullback.diagonal_fst pZ) r with he
  -- `w := a ≫ π_r`, `u₀ := a` as a morphism of `Over Z`, `ψ₀` := the pullback of the universal based jet along `a`
  have hw : (a.1 ≫ jetScheme.proj (k := k) r pZ) ≫ pZ = T.hom :=
    (CategoryTheory.Category.assoc _ _ _).trans a.2
  have hw' : (f.left ≫ a.1 ≫ jetScheme.proj (k := k) r pZ) ≫ pZ = T'.hom := by
    rw [CategoryTheory.Category.assoc, hw]; exact CategoryTheory.Over.w f
  let u₀ : CategoryTheory.Over.mk (a.1 ≫ jetScheme.proj (k := k) r pZ) ⟶ jetScheme.diagonalJet (k := k) r pZ :=
    CategoryTheory.Over.homMk a.1 rfl
  let g : CategoryTheory.Over.mk (f.left ≫ a.1 ≫ jetScheme.proj (k := k) r pZ) ⟶
      CategoryTheory.Over.mk (a.1 ≫ jetScheme.proj (k := k) r pZ) :=
    CategoryTheory.Over.homMk f.left rfl
  have hL := jetScheme.homEquivToFun_val (k := k) r pZ T'.left T'.hom
    ⟨f.left ≫ a.1, by rw [CategoryTheory.Category.assoc, a.2]; exact CategoryTheory.Over.w f⟩
    (f.left ≫ a.1 ≫ jetScheme.proj (k := k) r pZ) hw' (g ≫ u₀) rfl
  have hnat := e.homEquiv_comp g u₀
  show (jetScheme.homEquivToFun (k := k) r pZ T'.left T'.hom ⟨f.left ≫ a.1, _⟩).1 =
    jetThickeningMap (k := k) r f.left ≫
      (jetThickening.congrIso (k := k) r T.left _ _ (jetScheme.homEquiv_over (k := k) pZ T.left T.hom _ hw)).hom ≫
        (e.homEquiv (X := CategoryTheory.Over.mk (a.1 ≫ jetScheme.proj (k := k) r pZ)) u₀).1 ≫
          CategoryTheory.Limits.pullback.snd pZ pZ
  rw [hL]
  show (jetThickening.congrIso (k := k) r T'.left _ _ (jetScheme.homEquiv_over (k := k) pZ T'.left T'.hom _ hw')).hom ≫
      (e.homEquiv (X := CategoryTheory.Over.mk (f.left ≫ a.1 ≫ jetScheme.proj (k := k) r pZ)) (g ≫ u₀)).1 ≫
        CategoryTheory.Limits.pullback.snd pZ pZ = _
  rw [hnat, ← jetThickening.congrIso_hom_jetThickeningMap_assoc (k := k) r f.left
    (T'.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    ((f.left ≫ a.1 ≫ jetScheme.proj (k := k) r pZ) ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    ((a.1 ≫ jetScheme.proj (k := k) r pZ) ≫ pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (jetScheme.homEquiv_over (k := k) pZ T'.left T'.hom _ hw')
    (jetScheme.homEquiv_over (k := k) pZ T.left T.hom _ hw)
    ⟨CategoryTheory.Over.w_assoc f _⟩
    (@CategoryTheory.HomIsOver.mk _ _ T'.left T.left f.left (AlgebraicGeometry.Spec (CommRingCat.of k)) ⟨_⟩ ⟨_⟩
      (CategoryTheory.Category.assoc _ _ _).symm)]
  rfl

/-- Representability (relative version of Ein–Mustață Prop. 2.2 and Lemma 2.3), assembled from
`jetScheme.homEquiv` and `jetScheme.homEquiv_comp`; the representing object is `Over.mk (jetScheme.proj ≫ pZ)`.
The hypothesis `[AlgebraicGeometry.IsAffineHom pZ]` is needed since `jetScheme r pZ` is defined through the glued
construction `relativeJetScheme`, which requires `Z` affine over `S`. -/

theorem jetFunctor_isRepresentable {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ] :
    (jetFunctor (k := k) r pZ).IsRepresentable :=
  CategoryTheory.Functor.RepresentableBy.isRepresentable
    { homEquiv := fun {T} =>
        (CategoryTheory.Over.homEquivSubtypeOverMk
          (jetScheme.proj (k := k) r pZ ≫ pZ) T).trans
          (jetScheme.homEquiv (k := k) r pZ T.left T.hom)
      homEquiv_comp := fun {T T'} f g => by
        apply Subtype.ext
        exact jetScheme.homEquiv_comp (k := k) r pZ f ⟨g.left, CategoryTheory.Over.w g⟩ }

/-- `J_r(g)`: the universal jet of `Z` (`homEquiv` at `𝟙`) composed with `g` is a jet of `W`, and the inverse of
`homEquiv` for `J_r(W/S)` turns it into a morphism. -/

noncomputable def jetScheme.map {k : Type u} [Field k] {S Z W : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) {pZ : Z ⟶ S} {pW : W ⟶ S}
    [AlgebraicGeometry.IsAffineHom pZ] [AlgebraicGeometry.IsAffineHom pW]
    (g : Z ⟶ W) (hg : g ≫ pW = pZ) : jetScheme (k := k) r pZ ⟶ jetScheme (k := k) r pW :=
  let t := jetScheme.proj (k := k) r pZ ≫ pZ
  let u := jetScheme.homEquiv (k := k) r pZ (jetScheme (k := k) r pZ) t
    ⟨CategoryTheory.CategoryStruct.id _, CategoryTheory.Category.id_comp _⟩
  ((jetScheme.homEquiv (k := k) r pW (jetScheme (k := k) r pZ) t).symm
    ⟨u.1 ≫ g, (CategoryTheory.Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) hg).trans u.2)⟩).1

theorem jetScheme.homEquiv_proj {k : Type u} [Field k] {S Z : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (r : ℕ) (pZ : Z ⟶ S)
    [AlgebraicGeometry.IsAffineHom pZ]
    (T : AlgebraicGeometry.Scheme.{u}) (t : T ⟶ S)
    (a : { a : T ⟶ jetScheme (k := k) r pZ // a ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t }) :
    letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    a.1 ≫ jetScheme.proj (k := k) r pZ = jetConstantTerm (k := k) r T ≫ (jetScheme.homEquiv (k := k) r pZ T t a).1 := by
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨pZ ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ)).hom :=
    jetScheme.isAffineHom_fst pZ
  exact (jetScheme.homEquiv_toFun_constantTerm (k := k) pZ r T t
    (a.1 ≫ jetScheme.proj (k := k) r pZ)
    (jetScheme.homEquiv_over (k := k) pZ T t _ ((CategoryTheory.Category.assoc _ _ _).trans a.2))
    _ ((relativeJetScheme.representableBy (k := k)
        (CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst pZ pZ))
        (CategoryTheory.Limits.pullback.diagonal pZ)
        (CategoryTheory.Limits.pullback.diagonal_fst pZ) r).homEquiv
      (X := CategoryTheory.Over.mk (a.1 ≫ jetScheme.proj (k := k) r pZ))
      (CategoryTheory.Over.homMk
        (U := CategoryTheory.Over.mk (a.1 ≫ jetScheme.proj (k := k) r pZ))
        (V := jetScheme.diagonalJet (k := k) r pZ) a.1 rfl)).2.2).symm

end
