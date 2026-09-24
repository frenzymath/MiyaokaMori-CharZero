import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetConstantTerm
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetFunctor
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.UnbasedRelativeJetScheme

/-! # Based jets as the fiber along the section

Fixing the constant term is taking the fiber along the section: `J_r^s(Z/C)` is the pullback of the unbased jet
scheme `J_r(Z/C)` along `s : C → Z` (§2 of the paper, the definition of `J_k^s` as a fiber product).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The comparison morphism `J_r^s(Z/C) → J_r(Z/C)`. Construction: `J := relativeJetScheme` (the glued
construction) with representability data `e`; the universal based jet `u := e.homEquiv (𝟙 J)`,
`u.1 : J ×_k D_r → Z`, satisfies `u.2.1` (it lies over `C`); forgetting the based condition it is an (unbased) jet
on `J`, which corresponds under the inverse of `jetScheme.homEquiv` (with `T := J`, `t :=` the structure morphism
of `J`) to a morphism `J → J_r(Z/C)`. -/

noncomputable def relativeJetScheme.toUnbased {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    (relativeJetScheme (k := k) Z s hs r).left ⟶ jetScheme (k := k) r Z.hom :=
  let J := relativeJetScheme (k := k) Z s hs r
  let e := relativeJetScheme.representableBy (k := k) Z s hs r
  letI : J.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let u := e.homEquiv (CategoryTheory.CategoryStruct.id J)
  ((jetScheme.homEquiv (k := k) r Z.hom J.left J.hom).symm ⟨u.1, u.2.1⟩).1

section PullbackProof

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
  (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- `toUnbased` lies over the structure morphism of `J^s`: `toUnbased ≫ π_r ≫ Z.hom = J^s.hom` (the second
component of the subtype in `jetScheme.homEquiv`). -/

theorem relativeJetScheme.toUnbased_over :
    relativeJetScheme.toUnbased (k := k) Z s hs r ≫ jetScheme.proj (k := k) r Z.hom ≫ Z.hom =
      (relativeJetScheme (k := k) Z s hs r).hom :=
  let J := relativeJetScheme (k := k) Z s hs r
  let e := relativeJetScheme.representableBy (k := k) Z s hs r
  letI : J.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let u := e.homEquiv (CategoryTheory.CategoryStruct.id J)
  ((jetScheme.homEquiv (k := k) r Z.hom J.left J.hom).symm ⟨u.1, u.2.1⟩).2

/-- The (unbased) jet corresponding to `toUnbased` is the universal based jet with the based condition forgotten:
`homEquiv ⟨toUnbased, _⟩ = u` (`Equiv.apply_symm_apply`). -/

theorem relativeJetScheme.homEquiv_toUnbased :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (jetScheme.homEquiv (k := k) r Z.hom (relativeJetScheme (k := k) Z s hs r).left
        (relativeJetScheme (k := k) Z s hs r).hom
        ⟨relativeJetScheme.toUnbased (k := k) Z s hs r, relativeJetScheme.toUnbased_over (k := k) Z s hs r⟩).1 =
      ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv
        (CategoryTheory.CategoryStruct.id (relativeJetScheme (k := k) Z s hs r))).1 :=
  congrArg Subtype.val ((jetScheme.homEquiv (k := k) r Z.hom _ _).apply_symm_apply _)

/-- The square commutes: `toUnbased ≫ π_r = J^s.hom ≫ s`. `π_r` corresponds to taking the constant term
(`jetScheme.homEquiv_proj`), and the constant term of the universal based jet is `J^s.hom ≫ s`. -/

theorem relativeJetScheme.toUnbased_proj :
    relativeJetScheme.toUnbased (k := k) Z s hs r ≫ jetScheme.proj (k := k) r Z.hom =
      (relativeJetScheme (k := k) Z s hs r).hom ≫ s := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have h := jetScheme.homEquiv_proj (k := k) r Z.hom (relativeJetScheme (k := k) Z s hs r).left
    (relativeJetScheme (k := k) Z s hs r).hom
    ⟨relativeJetScheme.toUnbased (k := k) Z s hs r, relativeJetScheme.toUnbased_over (k := k) Z s hs r⟩
  rw [h, relativeJetScheme.homEquiv_toUnbased (k := k) Z s hs r]
  exact ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv
    (CategoryTheory.CategoryStruct.id (relativeJetScheme (k := k) Z s hs r))).2.2

/-- Pulling back along `v : T ⟶ J^s`: the jet corresponding to `v.left ≫ toUnbased` is `e.homEquiv v` with the based
condition forgotten (the two naturality statements `jetScheme.homEquiv_comp` and `e.homEquiv_comp`). -/

theorem relativeJetScheme.homEquiv_comp_toUnbased {T : CategoryTheory.Over C}
    (v : T ⟶ relativeJetScheme (k := k) Z s hs r) :
    letI : T.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨T.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (jetScheme.homEquiv (k := k) r Z.hom T.left T.hom
        ⟨v.left ≫ relativeJetScheme.toUnbased (k := k) Z s hs r, by
          rw [CategoryTheory.Category.assoc, relativeJetScheme.toUnbased_over]
          exact CategoryTheory.Over.w v⟩).1 =
      ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv v).1 := by
  letI : T.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨T.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : v.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc v _⟩
  have h1 := jetScheme.homEquiv_comp (k := k) r Z.hom v
    ⟨relativeJetScheme.toUnbased (k := k) Z s hs r, relativeJetScheme.toUnbased_over (k := k) Z s hs r⟩
  have h3 : (relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv v =
      (relativeJetFunctor (k := k) Z s hs r).map v.op
        ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv
          (CategoryTheory.CategoryStruct.id (relativeJetScheme (k := k) Z s hs r))) := by
    rw [← (relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv_comp v
      (CategoryTheory.CategoryStruct.id _), CategoryTheory.Category.comp_id]
  rw [h1, relativeJetScheme.homEquiv_toUnbased (k := k) Z s hs r, h3]
  rfl

include hs in
/-- Test data for the pullback cone: `a : T ⟶ J_r(Z/C)`, `c : T ⟶ C` with `a ≫ π_r = c ≫ s`; then `a` lies over `c`
(`hs`). -/
theorem relativeJetScheme.lift_over {T : AlgebraicGeometry.Scheme.{u}}
    (a : T ⟶ jetScheme (k := k) r Z.hom) (c : T ⟶ C)
    (h : a ≫ jetScheme.proj (k := k) r Z.hom = c ≫ s) :
    a ≫ jetScheme.proj (k := k) r Z.hom ≫ Z.hom = c := by
  rw [← CategoryTheory.Category.assoc, h, CategoryTheory.Category.assoc, hs,
    CategoryTheory.Category.comp_id]

/-- The based jet given by test data `(a, c)`: the jet `γ` corresponding to `a`, whose constant term is
`a ≫ π_r = c ≫ s`. -/

noncomputable def relativeJetScheme.basedJetOfLift {T : AlgebraicGeometry.Scheme.{u}}
    (a : T ⟶ jetScheme (k := k) r Z.hom) (c : T ⟶ C)
    (h : a ≫ jetScheme.proj (k := k) r Z.hom = c ≫ s) :
    (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op (CategoryTheory.Over.mk c)) :=
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨c ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let γ := jetScheme.homEquiv (k := k) r Z.hom T c ⟨a, relativeJetScheme.lift_over (k := k) Z s hs r a c h⟩
  ⟨γ.1, γ.2, by
    show jetConstantTerm (k := k) r T ≫ γ.1 = c ≫ s
    rw [← jetScheme.homEquiv_proj (k := k) r Z.hom T c
      ⟨a, relativeJetScheme.lift_over (k := k) Z s hs r a c h⟩]
    exact h⟩

/-- The lift `T ⟶ J^s`, given by the representability data `e` of the based jet functor. -/

noncomputable def relativeJetScheme.pullbackLift {T : AlgebraicGeometry.Scheme.{u}}
    (a : T ⟶ jetScheme (k := k) r Z.hom) (c : T ⟶ C)
    (h : a ≫ jetScheme.proj (k := k) r Z.hom = c ≫ s) :
    T ⟶ (relativeJetScheme (k := k) Z s hs r).left :=
  ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv.symm
    (relativeJetScheme.basedJetOfLift (k := k) Z s hs r a c h)).left

theorem relativeJetScheme.pullbackLift_hom {T : AlgebraicGeometry.Scheme.{u}}
    (a : T ⟶ jetScheme (k := k) r Z.hom) (c : T ⟶ C)
    (h : a ≫ jetScheme.proj (k := k) r Z.hom = c ≫ s) :
    relativeJetScheme.pullbackLift (k := k) Z s hs r a c h ≫ (relativeJetScheme (k := k) Z s hs r).hom = c :=
  CategoryTheory.Over.w _

/-- The key equivalence: for a morphism `v : Over.mk c ⟶ J^s` in `Over C`, `v.left ≫ toUnbased = a` if and only if
`e.homEquiv v = basedJetOfLift a c h`. -/

theorem relativeJetScheme.comp_toUnbased_eq_iff {T : AlgebraicGeometry.Scheme.{u}}
    (a : T ⟶ jetScheme (k := k) r Z.hom) (c : T ⟶ C)
    (h : a ≫ jetScheme.proj (k := k) r Z.hom = c ≫ s)
    (v : CategoryTheory.Over.mk c ⟶ relativeJetScheme (k := k) Z s hs r) :
    v.left ≫ relativeJetScheme.toUnbased (k := k) Z s hs r = a ↔
      (relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv v =
        relativeJetScheme.basedJetOfLift (k := k) Z s hs r a c h := by
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨c ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have key : (jetScheme.homEquiv (k := k) r Z.hom T c
      ⟨v.left ≫ relativeJetScheme.toUnbased (k := k) Z s hs r, by
        rw [CategoryTheory.Category.assoc, relativeJetScheme.toUnbased_over]
        exact CategoryTheory.Over.w v⟩).1 =
      ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv v).1 :=
    relativeJetScheme.homEquiv_comp_toUnbased (k := k) Z s hs r v
  constructor
  · intro hv
    apply Subtype.ext
    rw [← key]
    show _ = (jetScheme.homEquiv (k := k) r Z.hom T c
      ⟨a, relativeJetScheme.lift_over (k := k) Z s hs r a c h⟩).1
    congr 2
    exact Subtype.ext hv
  · intro hv
    have h2 : (jetScheme.homEquiv (k := k) r Z.hom T c
        ⟨v.left ≫ relativeJetScheme.toUnbased (k := k) Z s hs r, by
          rw [CategoryTheory.Category.assoc, relativeJetScheme.toUnbased_over]
          exact CategoryTheory.Over.w v⟩) =
        jetScheme.homEquiv (k := k) r Z.hom T c
          ⟨a, relativeJetScheme.lift_over (k := k) Z s hs r a c h⟩ := by
      apply Subtype.ext
      rw [key, hv]
      rfl
    exact congrArg Subtype.val ((jetScheme.homEquiv (k := k) r Z.hom T c).injective h2)

theorem relativeJetScheme.pullbackLift_toUnbased {T : AlgebraicGeometry.Scheme.{u}}
    (a : T ⟶ jetScheme (k := k) r Z.hom) (c : T ⟶ C)
    (h : a ≫ jetScheme.proj (k := k) r Z.hom = c ≫ s) :
    relativeJetScheme.pullbackLift (k := k) Z s hs r a c h ≫ relativeJetScheme.toUnbased (k := k) Z s hs r = a :=
  (relativeJetScheme.comp_toUnbased_eq_iff (k := k) Z s hs r a c h _).2
    ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv.apply_symm_apply _)

theorem relativeJetScheme.pullbackLift_uniq {T : AlgebraicGeometry.Scheme.{u}}
    (a : T ⟶ jetScheme (k := k) r Z.hom) (c : T ⟶ C)
    (h : a ≫ jetScheme.proj (k := k) r Z.hom = c ≫ s)
    (m : T ⟶ (relativeJetScheme (k := k) Z s hs r).left)
    (hm1 : m ≫ relativeJetScheme.toUnbased (k := k) Z s hs r = a)
    (hm2 : m ≫ (relativeJetScheme (k := k) Z s hs r).hom = c) :
    m = relativeJetScheme.pullbackLift (k := k) Z s hs r a c h := by
  let v : CategoryTheory.Over.mk c ⟶ relativeJetScheme (k := k) Z s hs r :=
    CategoryTheory.Over.homMk m hm2
  have hv : (relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv v =
      relativeJetScheme.basedJetOfLift (k := k) Z s hs r a c h :=
    (relativeJetScheme.comp_toUnbased_eq_iff (k := k) Z s hs r a c h v).1 hm1
  have hv' : v = (relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv.symm
      (relativeJetScheme.basedJetOfLift (k := k) Z s hs r a c h) :=
    (Equiv.eq_symm_apply _).2 hv
  exact congrArg CategoryTheory.CommaMorphism.left hv'

end PullbackProof

/-- **Fixing the constant term is taking the fiber along the section** (§2 of the paper): `J_r^s(Z/C)` is the
pullback of `J_r(Z/C)` along `s`.
Proof: compare the functors of points of the two jet functors directly. Commutativity is `toUnbased_proj` (`π_r`
corresponds to taking the constant term, `jetScheme.homEquiv_proj`, and the constant term of the universal based jet
is `J^s.hom ≫ s`). The lift `pullbackLift`: for test data `(a, c)` with `a ≫ π_r = c ≫ s`, the jet corresponding to
`a` has constant term `c ≫ s`, so it is a point of the based jet functor at `Over.mk c`, and the inverse of
`relativeJetScheme.representableBy` gives `T ⟶ J^s`. The two compatibilities and the uniqueness of the lift reduce
to `comp_toUnbased_eq_iff` (`v.left ≫ toUnbased = a ⇔ e.homEquiv v =` that based jet), which follows from the two
naturality statements `jetScheme.homEquiv_comp` and `e.homEquiv_comp`. Finally `PullbackCone.IsLimit.mk` and
`IsPullback.of_isLimit`. -/

theorem relativeJetScheme_isPullback_unbased {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    CategoryTheory.IsPullback (relativeJetScheme.toUnbased (k := k) Z s hs r) (relativeJetScheme (k := k) Z s hs r).hom
      (jetScheme.proj (k := k) r Z.hom) s :=
  CategoryTheory.IsPullback.of_isLimit
    (CategoryTheory.Limits.PullbackCone.IsLimit.mk (relativeJetScheme.toUnbased_proj (k := k) Z s hs r)
      (fun σ => relativeJetScheme.pullbackLift (k := k) Z s hs r σ.fst σ.snd σ.condition)
      (fun σ => relativeJetScheme.pullbackLift_toUnbased (k := k) Z s hs r σ.fst σ.snd σ.condition)
      (fun σ => relativeJetScheme.pullbackLift_hom (k := k) Z s hs r σ.fst σ.snd σ.condition)
      (fun σ m hm1 hm2 => relativeJetScheme.pullbackLift_uniq (k := k) Z s hs r σ.fst σ.snd σ.condition m hm1 hm2))

end
