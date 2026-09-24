import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldSections

/-! # Local sections of Cartier divisors: helper API

Helper API for the local uniqueness of Cartier divisors: local unit lifts in the quotient sheaf, gluing of
the sections chosen by `ofLocalData`, and extraction of local representatives.
1. The quotient of sheaves of commutative groups is the cokernel in `AddCommGrpCat`, and stalk exactness
   gives local lifts.
2. Global sections of the quotient sheaf are constructed from the unit ratios of local data and the sheaf
   condition.
3. Unfolding the `Classical.epsilon` in `ofLocalData` extracts a local representative at each point.
Source: Stacks 01X5.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry Classical

noncomputable section

namespace CartierToWeilQuotientUnitRatio

variable {k : Type u} [Field k]
variable {V : Variety k} [IsIntegral V.toScheme] [IsLocallyNoetherian V.toScheme]

abbrev I (V : Variety k) :=
  AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits V.toScheme
abbrev Q (V : Variety k) := TopCat.Sheaf.quotient (I V)
abbrev qpi (V : Variety k) := TopCat.Sheaf.quotientπ (I V)

abbrev E (V : Variety k) := sheafCompose
  (Opens.grothendieckTopology (V.toScheme : TopCat))
  commGroupAddCommGroupEquivalence.functor

private theorem local_lift_of_cokernel {A B : TopCat.Sheaf AddCommGrpCat.{u} (V.toScheme : TopCat)}
    (f : A ⟶ B) {U : Opens (V.toScheme : TopCat)} (x : V.toScheme) (hx : x ∈ U)
    (b : B.val.obj (op U))
    (hb : ((cokernel.π f).hom.app (op U)) b = 0) :
    ∃ (W : Opens (V.toScheme : TopCat)) (hWU : W ≤ U), x ∈ W ∧
      ∃ a : A.val.obj (op W),
        (f.hom.app (op W)) a = B.val.map (homOfLE hWU).op b := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (V.toScheme : TopCat)) :=
    ShortComplex.mk f (cokernel.π f) (by simp)
  have hS : S.Exact := ShortComplex.exact_cokernel f
  have hStalk : (S.map (TopCat.Sheaf.forget AddCommGrpCat (V.toScheme : TopCat) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := (V.toScheme : TopCat)) x)).Exact :=
    (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS x
  let gb := TopCat.Presheaf.germ B.val U x hx b
  have hgb : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat
      (X := (V.toScheme : TopCat)) x).map (cokernel.π f).hom) gb = 0 := by
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change (cokernel f).presheaf.germ U x hx (((cokernel.π f).hom.app (op U)) b) = 0
    rw [hb, map_zero]
  have hgb' : (S.map (TopCat.Sheaf.forget AddCommGrpCat (V.toScheme : TopCat) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := (V.toScheme : TopCat)) x)).g gb = 0 := by
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat
      (X := (V.toScheme : TopCat)) x).map (cokernel.π f).hom) gb = 0
    exact hgb
  obtain ⟨ga, hga⟩ := (ShortComplex.ab_exact_iff _).mp hStalk gb hgb'
  obtain ⟨V', hVU, hxV, a, ha⟩ :=
    TopCat.Presheaf.exists_le_germ_eq A.val ga hx
  have hga' : TopCat.Presheaf.germ B.val V' x hxV ((f.hom.app (op V')) a) =
      TopCat.Presheaf.germ B.val U x hx b := by
    rw [← ha] at hga
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat
      (X := (V.toScheme : TopCat)) x).map f.hom)
      (TopCat.Presheaf.germ A.val V' x hxV a) = gb at hga
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hga
    simpa [gb] using hga
  obtain ⟨W, hxW, hWV, hWU, hW⟩ :=
    TopCat.Presheaf.germ_eq B.val x hxV hx _ _ hga'
  refine ⟨W, leOfHom hWU, hxW, ?_⟩
  refine ⟨A.presheaf.map hWV.op a, ?_⟩
  have hn := congrArg (fun z => z a) (f.hom.naturality hWV.op)
  have hn' : (f.hom.app (op W)) ((A.presheaf.map hWV.op) a) =
      (B.presheaf.map hWV.op) ((f.hom.app (op V')) a) := by
    simpa only [CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn
  calc
    (f.hom.app (op W)) ((A.presheaf.map hWV.op) a) =
        (B.presheaf.map hWV.op) ((f.hom.app (op V')) a) := hn'
    _ = (B.presheaf.map hWU.op) b := hW
    _ = B.presheaf.map (homOfLE (leOfHom hWU)).op b := by rfl

lemma quotient_section_to_additive {U : V.toScheme.Opens}
    (g : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    Additive.ofMul ((qpi V).hom.app (op U) g) =
      (cokernel.π ((E V).map (I V))).hom.app (op U)
        (Additive.ofMul g) := by
  unfold qpi TopCat.Sheaf.quotientπ
  dsimp
  rfl

lemma quotient_eq_zero_additive {U : V.toScheme.Opens}
    (g₁ g₂ : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U))
    (h : (qpi V).hom.app (op U) g₁ = (qpi V).hom.app (op U) g₂) :
    (cokernel.π ((E V).map (I V))).hom.app (op U)
        (Additive.ofMul g₁ - Additive.ofMul g₂) = 0 := by
  let q := (cokernel.π ((E V).map (I V))).hom.app (op U)
  have hmap : q (Additive.ofMul g₁ - Additive.ofMul g₂) =
      q (Additive.ofMul g₁) - q (Additive.ofMul g₂) :=
    map_sub q.hom (Additive.ofMul g₁) (Additive.ofMul g₂)
  rw [hmap]
  have h1 := quotient_section_to_additive (V := V) g₁
  have h2 := quotient_section_to_additive (V := V) g₂
  rw [← h1, ← h2]
  exact sub_eq_zero.mpr (congrArg Additive.ofMul h)

private lemma restriction_sub_to_div {U W : V.toScheme.Opens} (hWU : W ≤ U)
    (g₁ g₂ : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    Additive.toMul
      (((sheafCompose (Opens.grothendieckTopology (V.toScheme : TopCat))
        commGroupAddCommGroupEquivalence.functor).obj
          V.toScheme.rationalFunctionsUnitsSheaf).val.map (homOfLE hWU).op
        (Additive.ofMul g₁ - Additive.ofMul g₂)) =
      (V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op).hom g₁ /
        (V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op).hom g₂ := by
  let qmap :=
    (((sheafCompose (Opens.grothendieckTopology (V.toScheme : TopCat))
      commGroupAddCommGroupEquivalence.functor).obj
        V.toScheme.rationalFunctionsUnitsSheaf).val.map (homOfLE hWU).op).hom
  have hm := map_sub qmap (Additive.ofMul g₁) (Additive.ofMul g₂)
  change Additive.toMul (qmap (Additive.ofMul g₁ - Additive.ofMul g₂)) = _
  rw [show Additive.toMul (qmap (Additive.ofMul g₁ - Additive.ofMul g₂)) =
      Additive.toMul (qmap (Additive.ofMul g₁) - qmap (Additive.ofMul g₂)) by
        exact congrArg Additive.toMul hm]
  change Additive.toMul (Additive.ofMul
      ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op).hom g₁) -
      Additive.ofMul
      ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op).hom g₂)) = _
  change ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op).hom g₁ /
      (V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op).hom g₂) = _
  rfl

lemma local_unit_ratio_eq {U : V.toScheme.Opens} (hU : Nonempty U)
    (x : V.toScheme) (hx : x ∈ U)
    (g₁ g₂ : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U))
    (h : (qpi V).hom.app (op U) g₁ = (qpi V).hom.app (op U) g₂) :
    ∃ W : V.toScheme.Opens, ∃ hWU : W ≤ U, x ∈ W ∧
      ∃ a : (V.toScheme.presheaf.stalk x)ˣ,
        algebraMap (V.toScheme.presheaf.stalk x) V.toScheme.functionField
            (a : V.toScheme.presheaf.stalk x) =
          ((V.toScheme.rationalUnitsSectionToFunctionField U) g₁ : V.toScheme.functionField) /
            ((V.toScheme.rationalUnitsSectionToFunctionField U) g₂ : V.toScheme.functionField) := by
  change Units (V.toScheme.rationalFunctionsSheaf.val.obj (op U)) at g₁ g₂
  let A := (E V).obj V.toScheme.unitsSheaf
  let B := (E V).obj V.toScheme.rationalFunctionsUnitsSheaf
  let f := (E V).map (I V)
  have hb0 := quotient_eq_zero_additive (V := V) g₁ g₂ h
  obtain ⟨W, hWU, hxW, a, ha⟩ := local_lift_of_cokernel (V := V) f x hx
    (Additive.ofMul g₁ - Additive.ofMul g₂) hb0
  letI : Nonempty W := ⟨⟨x, hxW⟩⟩
  let u : V.toScheme.unitsSheaf.val.obj (op W) := Additive.toMul a
  change (Γ(V.toScheme, W))ˣ at u
  have ha' := congrArg Additive.toMul ha
  let au : (V.toScheme.presheaf.stalk x)ˣ :=
    Units.map (V.toScheme.presheaf.germ W x hxW).hom.toMonoidHom
      u
  refine ⟨W, hWU, hxW, au, ?_⟩
  change algebraMap (V.toScheme.presheaf.stalk x) V.toScheme.functionField
      ((V.toScheme.presheaf.germ W x hxW).hom
        u.1) = _
  rw [V.toScheme.algebraMap_germ_eq_germToFunctionField hxW]
  dsimp [f, E] at ha'
  have hleft : Additive.toMul ((f.hom.app (op W)) a) = (I V).hom.app (op W) u := by
    rfl
  have hratio := restriction_sub_to_div (V := V) hWU g₁ g₂
  have ha_map : Additive.toMul ((f.hom.app (op W)) a) =
      Additive.toMul
        (((sheafCompose (Opens.grothendieckTopology (V.toScheme : TopCat))
          commGroupAddCommGroupEquivalence.functor).obj
            V.toScheme.rationalFunctionsUnitsSheaf).val.map (homOfLE hWU).op
          (Additive.ofMul g₁ - Additive.ofMul g₂)) := by
    exact ha'
  have ha'' : (I V).hom.app (op W) u =
      ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op).hom g₁) /
        ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op).hom g₂) := by
    have hleft' : (I V).hom.app (op W) u =
        Additive.toMul ((f.hom.app (op W)) a) := hleft.symm
    exact hleft'.trans (ha_map.trans hratio)
  have hres1 :
      (V.toScheme.rationalUnitsSectionToFunctionField W)
          ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op).hom g₁) =
        V.toScheme.rationalUnitsSectionToFunctionField U g₁ := by
    apply Units.ext
    change (V.toScheme.rationalSectionToFunctionField W).hom
        ((V.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU).op).hom g₁.1) =
      (V.toScheme.rationalSectionToFunctionField U).hom g₁.1
    have hn := congrArg (fun z => z g₁.1)
      (V.toScheme.rationalSectionToFunctionField_res U W hWU)
    simpa only [CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn
  have hres2 :
      (V.toScheme.rationalUnitsSectionToFunctionField W)
          ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op).hom g₂) =
        V.toScheme.rationalUnitsSectionToFunctionField U g₂ := by
    apply Units.ext
    change (V.toScheme.rationalSectionToFunctionField W).hom
        ((V.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU).op).hom g₂.1) =
      (V.toScheme.rationalSectionToFunctionField U).hom g₂.1
    have hn := congrArg (fun z => z g₂.1)
      (V.toScheme.rationalSectionToFunctionField_res U W hWU)
    simpa only [CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn
  have hfield := congrArg
    (V.toScheme.rationalUnitsSectionToFunctionField W) ha''
  rw [map_div, hres1, hres2] at hfield
  have hfield_val := congrArg Units.val hfield
  have hmapW0 :
      ((V.toScheme.rationalUnitsSectionToFunctionField W)
        ((I V).hom.app (op W) u)).val =
        (V.toScheme.rationalSectionToFunctionField W).hom
          (((I V).hom.app (op W) u).val) := by rfl
  have hmapU10 :
      ((V.toScheme.rationalUnitsSectionToFunctionField U) g₁).val =
        (V.toScheme.rationalSectionToFunctionField U).hom g₁.val := by rfl
  have hmapU20 :
      ((V.toScheme.rationalUnitsSectionToFunctionField U) g₂).val =
        (V.toScheme.rationalSectionToFunctionField U).hom g₂.val := by rfl
  rw [hmapW0] at hfield_val
  change (V.toScheme.rationalSectionToFunctionField W).hom
      ((I V).hom.app (op W) u).val = _ at hfield_val
  have hvaldiv :
      (((V.toScheme.rationalUnitsSectionToFunctionField U) g₁ /
          (V.toScheme.rationalUnitsSectionToFunctionField U) g₂ :
          V.toScheme.functionFieldˣ) : V.toScheme.functionField) =
        ((V.toScheme.rationalUnitsSectionToFunctionField U) g₁ :
          V.toScheme.functionField) /
          ((V.toScheme.rationalUnitsSectionToFunctionField U) g₂ :
            V.toScheme.functionField) := by
    simpa only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hvaldiv, hmapU10, hmapU20] at hfield_val
  have hu : ((I V).hom.app (op W) u).val =
      (V.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom u.val := by rfl
  have hmap := AlgebraicGeometry.Scheme.toRationalFunctionsSheaf_rationalSectionToFunctionField
    V.toScheme W
  have hmap' := congrArg (fun z => z u.val) hmap
  change (V.toScheme.rationalSectionToFunctionField W).hom
      ((V.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom u.val) =
    V.toScheme.germToFunctionField W u.val at hmap'
  rw [hu, hmap'] at hfield_val
  have hga := V.toScheme.algebraMap_germ_eq_germToFunctionField hxW u.val
  calc
    V.toScheme.germToFunctionField W u.val =
        algebraMap (V.toScheme.presheaf.stalk x) V.toScheme.functionField
          ((V.toScheme.presheaf.germ W x hxW).hom u.val) := hga.symm
    _ = _ := hga.trans (by simpa only [hmapU10, hmapU20] using hfield_val)

end CartierToWeilQuotientUnitRatio

namespace CartierToWeilEpsilon

open AlgebraicGeometry.Intersection

variable {k : Type u} [Field k]
variable {V : Variety k} [AlgebraicGeometry.IsIntegral V.toScheme]
  [AlgebraicGeometry.IsLocallyNoetherian V.toScheme]

abbrev I (V : Variety k) :=
  AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits V.toScheme
abbrev Q (V : Variety k) := TopCat.Sheaf.quotient (I V)
abbrev qpi (V : Variety k) := TopCat.Sheaf.quotientπ (I V)

private theorem quotient_kills_unit (U : V.toScheme.Opens)
    (u : V.toScheme.unitsSheaf.val.obj (Opposite.op U)) :
    ((qpi V).hom.app (Opposite.op U)) ((I V).hom.app (Opposite.op U) u) = 1 := by
  unfold qpi TopCat.Sheaf.quotientπ
  dsimp
  let E := CategoryTheory.sheafCompose (Opens.grothendieckTopology (V.toScheme : TopCat))
    commGroupAddCommGroupEquivalence.functor
  let Einv := CategoryTheory.sheafCompose (Opens.grothendieckTopology (V.toScheme : TopCat))
    commGroupAddCommGroupEquivalence.inverse
  let j := E.map (I V)
  have hc := CategoryTheory.Limits.cokernel.condition j
  have hcU := congrArg
    (fun z : E.obj V.toScheme.unitsSheaf ⟶ (CategoryTheory.Limits.cokernel j) =>
      z.hom.app (op U)) hc
  have hcU' := congrArg (fun z => z (Additive.ofMul u)) hcU
  have hcU'' := congrArg (fun z => Additive.toMul z) hcU'
  change Additive.toMul
      (((Einv.map (cokernel.π j)).hom.app (op U))
        (((E.map (I V)).hom.app (op U)) (Additive.ofMul u))) = _
  change Additive.toMul
      (((Einv.map (cokernel.π j)).hom.app (op U))
        (((E.map (I V)).hom.app (op U)) (Additive.ofMul u))) =
      Additive.toMul (((InducedCategory.Hom.hom
        (0 : E.obj V.toScheme.unitsSheaf ⟶ CategoryTheory.Limits.cokernel j)).app (op U))
        (Additive.ofMul u)) at hcU''
  have hz :
      Additive.toMul (((InducedCategory.Hom.hom
        (0 : E.obj V.toScheme.unitsSheaf ⟶ CategoryTheory.Limits.cokernel j)).app (op U))
        (Additive.ofMul u)) =
        (1 : (Einv.obj (CategoryTheory.Limits.cokernel j)).obj.obj (op U)) := by
    rfl
  rw [hz] at hcU''
  exact hcU''

private theorem rationalUnits_surj (U : V.toScheme.Opens) [hU : Nonempty U] :
    Function.Surjective (V.toScheme.rationalUnitsSectionToFunctionField U) := by
  intro a
  let φ := V.toScheme.rationalSectionToFunctionField U
  have hφ := AlgebraicGeometry.Scheme.rationalSectionToFunctionField_bijective
    V.toScheme U
  obtain ⟨t, ht⟩ := hφ.2 (a : V.toScheme.functionField)
  obtain ⟨ti, hti⟩ := hφ.2 (a.inv : V.toScheme.functionField)
  have hprod : t * ti = 1 := by
    apply hφ.1
    rw [map_mul, ht, hti]
    simpa using a.val_inv
  have hprod' : ti * t = 1 := by
    apply hφ.1
    rw [map_mul, hti, ht]
    simpa using a.inv_val
  let b : (V.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op U))ˣ :=
    { val := t, inv := ti, val_inv := hprod, inv_val := hprod' }
  refine ⟨b, ?_⟩
  apply Units.ext
  exact ht

theorem exists_quotient_section
    {ι : Type u} (U : ι → V.toScheme.Opens)
    (f : ι → (V.toScheme.functionField)ˣ)
    (hlocal : CartierDivisor.IsLocalData U f) :
    ∃ s : (Q V).val.obj (Opposite.op ⊤),
      ∀ i, ∀ hne : Nonempty (U i),
        ∃ t : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (Opposite.op (U i)),
          (haveI := hne; V.toScheme.rationalUnitsSectionToFunctionField (U i) t) = f i ∧
          (Q V).val.map (homOfLE (show U i ≤ ⊤ from le_top)).op s =
            (qpi V).hom.app (Opposite.op (U i)) t := by
  classical
  have hsurj (i : ι) (hne : Nonempty (U i)) :
      ∃ t : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (Opposite.op (U i)),
        (haveI := hne; V.toScheme.rationalUnitsSectionToFunctionField (U i) t) = f i := by
    letI := hne
    obtain ⟨t, ht⟩ := (rationalUnits_surj (V := V) (U i)) (f i)
    exact ⟨t, ht⟩
  let t : ∀ i, V.toScheme.rationalFunctionsUnitsSheaf.val.obj (Opposite.op (U i)) :=
    fun i => if h : Nonempty (U i) then Classical.choose (hsurj i h) else 1
  have ht (i : ι) (hne : Nonempty (U i)) :
      (haveI := hne; V.toScheme.rationalUnitsSectionToFunctionField (U i) (t i)) = f i := by
    dsimp [t]
    rw [dif_pos hne]
    exact Classical.choose_spec (hsurj i hne)
  have hcompat : (Q V).presheaf.IsCompatible U
      (fun i => (qpi V).hom.app (op (U i)) (t i)) := by
    intro i j
    by_cases hW : Nonempty (U i ⊓ U j : V.toScheme.Opens)
    · let W : V.toScheme.Opens := U i ⊓ U j
      letI : Nonempty W := hW
      let hi : W ≤ U i := inf_le_left
      let hj : W ≤ U j := inf_le_right
      let x := Classical.choice hW
      have hUi : Nonempty (U i) := ⟨⟨x.1, x.2.1⟩⟩
      have hUj : Nonempty (U j) := ⟨⟨x.1, x.2.2⟩⟩
      letI : Nonempty (U i) := hUi
      letI : Nonempty (U j) := hUj
      obtain ⟨u, hu⟩ := AlgebraicGeometry.Scheme.exists_unit_section_of_stalkwise_unit
        (X := V.toScheme) (U := W) (f i / f j : V.toScheme.functionField) (by
          intro y
          have hyi : y.1 ∈ U i := hi y.2
          have hyj : y.1 ∈ U j := hj y.2
          obtain ⟨uy, huy⟩ := (hlocal.2 i j y.1 ⟨hyi, hyj⟩).1
          have hdivval : ((f i / f j : (V.toScheme.functionField)ˣ) : V.toScheme.functionField) =
              (f i : V.toScheme.functionField) / (f j : V.toScheme.functionField) := by
            simpa only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
          exact ⟨uy, huy.trans hdivval⟩)
      have hres_i :
          (V.toScheme.rationalUnitsSectionToFunctionField W)
              ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hi).op) (t i)) =
            V.toScheme.rationalUnitsSectionToFunctionField (U i) (t i) := by
        apply Units.ext
        change (V.toScheme.rationalSectionToFunctionField W).hom
            ((V.toScheme.rationalFunctionsSheaf.val.map (homOfLE hi).op).hom (t i).val) =
          (V.toScheme.rationalSectionToFunctionField (U i)).hom (t i).val
        have hn := congrArg (fun z => z (t i).val)
          (V.toScheme.rationalSectionToFunctionField_res (U i) W hi)
        simpa only [CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn
      have hres_j :
          (V.toScheme.rationalUnitsSectionToFunctionField W)
              ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j)) =
            V.toScheme.rationalUnitsSectionToFunctionField (U j) (t j) := by
        apply Units.ext
        change (V.toScheme.rationalSectionToFunctionField W).hom
            ((V.toScheme.rationalFunctionsSheaf.val.map (homOfLE hj).op).hom (t j).val) =
          (V.toScheme.rationalSectionToFunctionField (U j)).hom (t j).val
        have hn := congrArg (fun z => z (t j).val)
          (V.toScheme.rationalSectionToFunctionField_res (U j) W hj)
        simpa only [CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn
      have hti : (V.toScheme.rationalUnitsSectionToFunctionField W)
          ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hi).op) (t i)) = f i := by
        rw [hres_i]
        exact ht i hUi
      have htj : (V.toScheme.rationalUnitsSectionToFunctionField W)
          ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j)) = f j := by
        rw [hres_j]
        exact ht j hUj
      have hmul :
          (V.toScheme.rationalUnitsSectionToFunctionField W)
              ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hi).op) (t i)) =
            (V.toScheme.rationalUnitsSectionToFunctionField W)
              ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j) *
                ((I V).hom.app (op W) u)) := by
        have hunit_ratio :
            (V.toScheme.rationalUnitsSectionToFunctionField W)
                ((I V).hom.app (op W) u) = f i / f j := by
          apply Units.ext
          have hmap_val :
              (((V.toScheme.rationalUnitsSectionToFunctionField W)
                ((I V).hom.app (op W) u)).val) =
                (V.toScheme.rationalSectionToFunctionField W).hom
                  (((I V).hom.app (op W) u).val) := by
            rfl
          rw [hmap_val]
          have hu0 : ((I V).hom.app (op W) u).val =
              (V.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom
                (u : Γ(V.toScheme, W)) := by
            rfl
          rw [hu0]
          have hm := AlgebraicGeometry.Scheme.toRationalFunctionsSheaf_rationalSectionToFunctionField
            V.toScheme W
          have hm' := congrArg (fun z => z (u : Γ(V.toScheme, W))) hm
          change (V.toScheme.rationalSectionToFunctionField W).hom
              ((V.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom
                (u : Γ(V.toScheme, W))) =
            V.toScheme.germToFunctionField W (u : Γ(V.toScheme, W)) at hm'
          have hdivval : ((f i / f j : (V.toScheme.functionField)ˣ) : V.toScheme.functionField) =
              (f i : V.toScheme.functionField) / (f j : V.toScheme.functionField) := by
            simpa only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
          rw [hm', hu, hdivval]
        rw [map_mul, htj, hunit_ratio]
        have hmul_units : f j * (f i / f j) = f i := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
        rw [hmul_units]
        exact hti
      have hsec :
          (V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hi).op) (t i) =
            (V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j) *
              ((I V).hom.app (op W) u) := by
        have hinj : Function.Injective
            (V.toScheme.rationalUnitsSectionToFunctionField W) := by
          intro a b hab
          apply Units.ext
          have hv := congrArg Units.val hab
          unfold AlgebraicGeometry.Scheme.rationalUnitsSectionToFunctionField at hv
          change (V.toScheme.rationalSectionToFunctionField W).hom a.val =
            (V.toScheme.rationalSectionToFunctionField W).hom b.val at hv
          exact (AlgebraicGeometry.Scheme.rationalSectionToFunctionField_bijective
            V.toScheme W).1 hv
        exact hinj hmul
      have hnat_i :
          (Q V).val.map (homOfLE hi).op ((qpi V).hom.app (op (U i)) (t i)) =
            (qpi V).hom.app (op W)
              ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hi).op) (t i)) := by
        have hn := congrArg (fun z => z (t i))
          ((qpi V).hom.naturality (homOfLE hi).op)
        simpa only [CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn.symm
      have hnat_j :
          (Q V).val.map (homOfLE hj).op ((qpi V).hom.app (op (U j)) (t j)) =
            (qpi V).hom.app (op W)
              ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j)) := by
        have hn := congrArg (fun z => z (t j))
          ((qpi V).hom.naturality (homOfLE hj).op)
        simpa only [CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn.symm
      calc
        (Q V).val.map (homOfLE hi).op ((qpi V).hom.app (op (U i)) (t i)) =
            (qpi V).hom.app (op W)
              ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hi).op) (t i)) := hnat_i
        _ = (qpi V).hom.app (op W)
              ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j) *
                ((I V).hom.app (op W) u)) := congrArg _ hsec
        _ = (qpi V).hom.app (op W)
              ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j)) := by
          let qW := (qpi V).hom.app (op W)
          have hkill : qW.hom ((I V).hom.app (op W) u) = 1 :=
            quotient_kills_unit (V := V) W u
          calc
            qW.hom ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j) *
                ((I V).hom.app (op W) u)) =
                qW.hom ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j)) *
                  qW.hom ((I V).hom.app (op W) u) := map_mul qW.hom _ _
            _ = qW.hom ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j)) * 1 := by
              rw [hkill]
            _ = qW.hom ((V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hj).op) (t j)) :=
              mul_one _
        _ = (Q V).val.map (homOfLE hj).op ((qpi V).hom.app (op (U j)) (t j)) := hnat_j.symm
    · haveI : Subsingleton ((Q V).val.obj (op (U i ⊓ U j : V.toScheme.Opens))) := by
        have hbot : U i ⊓ U j = ⊥ := by
          apply le_antisymm
          · intro x hx
            exact (hW ⟨⟨x, hx⟩⟩).elim
          · exact bot_le
        have hterm := (Q V).isTerminalOfEqEmpty hbot
        have hzero : IsZero ((Q V).obj.obj (op (U i ⊓ U j))) :=
          IsZero.of_iso (isZero_zero CommGrpCat.{u})
            (hterm.uniqueUpToIso (isZero_zero CommGrpCat.{u}).isTerminal)
        exact CommGrpCat.subsingleton_of_isZero hzero
      exact Subsingleton.elim _ _
  obtain ⟨s, hs, -⟩ := (Q V).existsUnique_gluing' U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top))
    (by rw [hlocal.1]) _ hcompat
  refine ⟨s, ?_⟩
  intro i hne
  exact ⟨t i, ht i hne, hs i⟩

end CartierToWeilEpsilon

namespace CartierToWeilLocalSection

variable {k : Type u} [Field k] {V : Variety k}

abbrev I (V : Variety k) :=
  AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits V.toScheme
abbrev Q (V : Variety k) := TopCat.Sheaf.quotient (I V)
abbrev qpi (V : Variety k) := TopCat.Sheaf.quotientπ (I V)

lemma local_section_ofLocalData
    {ι : Type u} (U : ι → V.toScheme.Opens)
    (f : ι → (V.toScheme.functionField)ˣ)
    (hUf : CartierDivisor.IsLocalData U f)
    (x : V.toScheme) (i : ι) (hxi : x ∈ U i) :
    ∃ t : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op (U i)),
      (haveI : Nonempty (U i) := ⟨⟨x, hxi⟩⟩;
        V.toScheme.rationalUnitsSectionToFunctionField (U i) t) = f i ∧
      (Q V).val.map (homOfLE (show U i ≤ ⊤ from le_top)).op
          (Additive.toMul (CartierDivisor.ofLocalData U f)) =
        (qpi V).hom.app (op (U i)) t := by
  classical
  let P : (Q V).val.obj (op ⊤) → Prop := fun s =>
    ∀ j, ∀ hne : Nonempty (U j),
      ∃ t : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op (U j)),
        (haveI := hne;
          V.toScheme.rationalUnitsSectionToFunctionField (U j) t) = f j ∧
        (Q V).val.map (homOfLE (show U j ≤ ⊤ from le_top)).op s =
          (qpi V).hom.app (op (U j)) t
  obtain ⟨s, hs⟩ :=
    CartierToWeilEpsilon.exists_quotient_section (V := V) U f hUf
  have heps : P (Classical.epsilon P) := Classical.epsilon_spec ⟨s, hs⟩
  have hrepr : Additive.toMul (CartierDivisor.ofLocalData U f) = Classical.epsilon P := by
    unfold CartierDivisor.ofLocalData
    dsimp
    change Additive.toMul (if CartierDivisor.IsLocalData U f then
      Additive.ofMul (Classical.epsilon P) else 0) = Classical.epsilon P
    rw [if_pos hUf]
    rfl
  rw [hrepr]
  exact heps i ⟨⟨x, hxi⟩⟩

end CartierToWeilLocalSection

end
