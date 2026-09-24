import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02uxFinGeneratedColimit
import MiyaokaMori.AlgebraicGeometry.Cohomology.ConstantSheaf.ConstantSheafSections

/-! # The unit section of `j_!ℤ_U` and morphisms out of `j_!ℤ_U`

Stacks 0A38 identifies a morphism `j_!ℤ_U ⟶ F` with a section of `F` over `U` (Stacks 00A5: `j_! ⊣ j^{-1}`, and
`ℤ_U ⊣ Γ(U, −)`). The surjective half (`sectionDesc F U s : j_!ℤ_U ⟶ F` with value `s` on the unit section
`unitSection U ∈ (j_!ℤ_U)(U)`, `sectionDesc_unitSection`) is in `Stacks02uxFinGeneratedColimit.lean`; here
we add the *injective* half and its consequences, formulated with sections:
* `extendConstSec U hV z ∈ (j_!ℤ_U)(V)` for `V ≤ U`: the constant section `z` (the image under `toSheafify` of the
  constant section `z ∈ ℤ_U(j⁻¹V)`, which lies in the presheaf `P(V) = ℤ_U(j⁻¹V)` because `V ≤ U`); it is
  compatible with restriction (`extendConstSec_res`) and additive in `z` (`zsmul_extendConstSec_one`);
  `unitSection U = extendConstSec U le_rfl 1` definitionally.
* `hom_ext_of_unitSection`: two morphisms `j_!ℤ_U ⟶ F` agreeing on the unit section are equal. Proof: a morphism
  out of the sheafification is determined by its restriction to `P` (`sheafify_hom_ext`); on `P(V)` (`V ≤ U`) a
  section `y ∈ ℤ_U(j⁻¹V)` is locally a constant section `z` (`exists_locally_constSec`), where it is `z` times the
  restriction of the unit section; conclude by separatedness of `F` (`TopCat.Sheaf.eq_of_locally_eq'`).
* `restrictExtend U h : j_!ℤ_W ⟶ j_!ℤ_U` for `W ≤ U`: the canonical map (`sectionDesc` of the restriction to `W`
  of the unit section of `j_!ℤ_U`), characterised by `restrictExtend_unitSection`: it sends the unit section of
  `j_!ℤ_W` to the restriction of the unit section of `j_!ℤ_U`; `sectionDesc_extendConstSec` computes any
  `sectionDesc F U s` on the constant sections.
* `isJointlyEpi_restrictExtend`: for an open cover `W_i` of `U` the maps `j_!ℤ_{W_i} ⟶ j_!ℤ_U` are jointly
  epimorphic (a morphism out of `j_!ℤ_U` is determined by its value on the unit section, which is determined by
  its restrictions to the `W_i`).

Source: Stacks 0A38, proof, paragraph 1; Stacks 00A5. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (U : Opens X)

/-- `W ≤ j⁻¹V` implies `j(W) ≤ V` -/
theorem functor_obj_le_of_le_map {W : Opens U} {V : Opens X}
    (h : W ≤ (Opens.map (Opens.inclusion' U)).obj V) : (Opens.isOpenEmbedding U).functor.obj W ≤ V := by
  rintro x ⟨q, hq, rfl⟩
  exact h hq

/-- an element of `ℤ_U(j⁻¹V)` as an element of the presheaf `P = extendByZeroPresheaf U ℤ_U` at `V ≤ U` -/
def extendByZeroPresheafMk {V : Opens X} (hV : V ≤ U)
    (y : (constZ U).obj.obj (op ((Opens.map (Opens.inclusion' U)).obj V))) :
    (extendByZeroPresheaf U (constZ U)).obj (op V) :=
  ⟨y, by
    show y ∈ extendByZeroSubgroup U (constZ U) (op V)
    unfold extendByZeroSubgroup
    rw [if_pos hV]
    exact AddSubgroup.mem_top _⟩

theorem extendByZeroPresheafMk_map {V V' : Opens X} (hV : V ≤ U) (φ : op V ⟶ op V')
    (y : (constZ U).obj.obj (op ((Opens.map (Opens.inclusion' U)).obj V))) :
    ((extendByZeroPresheaf U (constZ U)).map φ).hom (extendByZeroPresheafMk U hV y) =
      extendByZeroPresheafMk U (le_trans (leOfHom φ.unop) hV)
        (((constZ U).obj.map (homOfLE ((Opens.map (Opens.inclusion' U)).monotone (leOfHom φ.unop))).op).hom y) := by
  refine Subtype.ext ?_
  rfl

theorem extendByZeroPresheafMk_zsmul {V : Opens X} (hV : V ≤ U) (z : ℤ)
    (y : (constZ U).obj.obj (op ((Opens.map (Opens.inclusion' U)).obj V))) :
    extendByZeroPresheafMk U hV (z • y) = z • extendByZeroPresheafMk U hV y := by
  refine Subtype.ext ?_
  rfl

/-- `toSheafify` at `V`, with codomain written as `(j_!ℤ_U)(V)` -/
def extendConstSecHom (V : Opens X) :
    (extendByZeroPresheaf U (constZ U)).obj (op V) ⟶ (extendByZeroConstant U).obj.obj (op V) :=
  (toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U (constZ U))).app (op V)

theorem extendConstSecHom_naturality {V V' : Opens X} (φ : op V ⟶ op V')
    (x : (extendByZeroPresheaf U (constZ U)).obj (op V)) :
    ((extendByZeroConstant U).obj.map φ).hom ((extendConstSecHom U V).hom x) =
      (extendConstSecHom U V').hom (((extendByZeroPresheaf U (constZ U)).map φ).hom x) := by
  have := congrArg (fun g => g.hom x)
    ((toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U (constZ U))).naturality φ)
  exact this.symm

/-- **the constant section `z` of `j_!ℤ_U` over `V ≤ U`** -/
def extendConstSec {V : Opens X} (hV : V ≤ U) (z : ℤ) : (extendByZeroConstant U).obj.obj (op V) :=
  (extendConstSecHom U V).hom (extendByZeroPresheafMk U hV (constSec _ z))

/-- the unit section `e_U ∈ (j_!ℤ_U)(U)` of `Stacks02uxFinGeneratedColimit.lean` is the constant section `1` -/
theorem unitSection_eq : unitSection U = extendConstSec U le_rfl 1 := rfl

theorem extendConstSec_res {V V' : Opens X} (hV : V ≤ U) (φ : op V ⟶ op V') (z : ℤ) :
    ((extendByZeroConstant U).obj.map φ).hom (extendConstSec U hV z) =
      extendConstSec U (le_trans (leOfHom φ.unop) hV) z := by
  unfold extendConstSec
  rw [extendConstSecHom_naturality, extendByZeroPresheafMk_map]
  erw [constSec_res]

theorem zsmul_extendConstSec_one {V : Opens X} (hV : V ≤ U) (z : ℤ) :
    z • extendConstSec U hV 1 = extendConstSec U hV z := by
  unfold extendConstSec
  rw [← map_zsmul, ← extendByZeroPresheafMk_zsmul]
  erw [zsmul_constSec_one]

/-- the section `z` over `V ≤ U` is `z` times the restriction of the unit section -/
theorem extendConstSec_eq_zsmul_res_unitSection {V : Opens X} (hV : V ≤ U) (z : ℤ) :
    extendConstSec U hV z =
      z • ((extendByZeroConstant U).obj.map (homOfLE hV).op).hom (unitSection U) := by
  rw [← zsmul_extendConstSec_one, unitSection_eq, extendConstSec_res]

/-- **hom-extensionality**: a morphism `j_!ℤ_U ⟶ F` is determined by its value on the unit section -/
theorem hom_ext_of_unitSection {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {f g : extendByZeroConstant U ⟶ F}
    (h : (f.hom.app (op U)).hom (unitSection U) = (g.hom.app (op U)).hom (unitSection U)) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  refine sheafify_hom_ext (Opens.grothendieckTopology X) (P := extendByZeroPresheaf U (constZ U)) _ _
    F.property ?_
  ext V x
  obtain ⟨V⟩ := V
  change (f.hom.app (op V)).hom ((extendConstSecHom U V).hom x) = (g.hom.app (op V)).hom ((extendConstSecHom U V).hom x)
  by_cases hV : V ≤ U
  · -- `x = ⟨y⟩` with `y ∈ ℤ_U(j⁻¹V)`, locally a constant section
    let y : (constZ U).obj.obj (op ((Opens.map (Opens.inclusion' U)).obj V)) := x.1
    have hx : x = extendByZeroPresheafMk U hV y := Subtype.ext rfl
    rw [hx]
    -- for every point `q ∈ j⁻¹V` choose a neighbourhood on which `y` is constant
    have hloc := fun q : {q : U // q ∈ (Opens.map (Opens.inclusion' U)).obj V} =>
      exists_locally_constSec (T := U) _ y q.1 q.2
    choose W' hW' hqW' z hz using hloc
    let W : {q : U // q ∈ (Opens.map (Opens.inclusion' U)).obj V} → Opens X :=
      fun q => (Opens.isOpenEmbedding U).functor.obj (W' q)
    have hWV : ∀ q, W q ≤ V := fun q => functor_obj_le_of_le_map U (hW' q)
    have hcover : V ≤ iSup W := by
      intro x hx
      rw [Opens.mem_iSup]
      exact ⟨⟨⟨x, hV hx⟩, hx⟩, ⟨⟨x, hV hx⟩, hqW' _, rfl⟩⟩
    refine TopCat.Sheaf.eq_of_locally_eq' F W V (fun q => homOfLE (hWV q)) hcover _ _ fun q => ?_
    -- on `W q` the section `y` restricts to the constant section `z q`
    have hres : ((extendByZeroPresheaf U (constZ U)).map (homOfLE (hWV q)).op).hom (extendByZeroPresheafMk U hV y) =
        extendByZeroPresheafMk U (le_trans (hWV q) hV) (constSec _ (z q)) := by
      rw [extendByZeroPresheafMk_map]
      congr 1
      have h1 : (Opens.map (Opens.inclusion' U)).obj (W q) ≤ W' q := le_of_eq (Opens.map_functor_eq (W' q))
      have h3 : (homOfLE ((Opens.map (Opens.inclusion' U)).monotone (hWV q))).op =
          (homOfLE (hW' q)).op ≫ (homOfLE h1).op :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      rw [h3]
      erw [← map_comp_hom_apply, hz q, constSec_res]
    have key : ∀ (φ : extendByZeroConstant U ⟶ F),
        (F.obj.map (homOfLE (hWV q)).op).hom ((φ.hom.app (op V)).hom ((extendConstSecHom U V).hom
          (extendByZeroPresheafMk U hV y))) =
        z q • (F.obj.map (homOfLE (le_trans (hWV q) hV)).op).hom ((φ.hom.app (op U)).hom (unitSection U)) := by
      intro φ
      have hnat := congrArg (fun g => g.hom ((extendConstSecHom U V).hom (extendByZeroPresheafMk U hV y)))
        (φ.hom.naturality (homOfLE (hWV q)).op)
      change (φ.hom.app (op (W q))).hom (((extendByZeroConstant U).obj.map (homOfLE (hWV q)).op).hom _) =
        (F.obj.map (homOfLE (hWV q)).op).hom ((φ.hom.app (op V)).hom _) at hnat
      rw [← hnat, extendConstSecHom_naturality, hres]
      change (φ.hom.app (op (W q))).hom (extendConstSec U _ (z q)) = _
      rw [extendConstSec_eq_zsmul_res_unitSection, map_zsmul]
      congr 1
      have hnat2 := congrArg (fun g => g.hom (unitSection U))
        (φ.hom.naturality (homOfLE (le_trans (hWV q) hV)).op)
      exact hnat2
    rw [key f, key g, h]
  · have hx : x = 0 := extendByZeroPresheaf_eq_zero_of_not_le U (op V) hV x
    rw [hx, map_zero, map_zero, map_zero]

/-- value of `sectionDesc F U s` on the constant section `z` over `V ≤ U`: `z • s|_V` -/
theorem sectionDesc_extendConstSec (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (s : F.obj.obj (op U)) {V : Opens X} (hV : V ≤ U) (z : ℤ) :
    ((sectionDesc F U s).hom.app (op V)).hom (extendConstSec U hV z) =
      z • (F.obj.map (homOfLE hV).op).hom s := by
  rw [extendConstSec_eq_zsmul_res_unitSection, map_zsmul]
  congr 1
  have hnat := congrArg (fun g => g.hom (unitSection U)) ((sectionDesc F U s).hom.naturality (homOfLE hV).op)
  change ((sectionDesc F U s).hom.app (op V)).hom (((extendByZeroConstant U).obj.map (homOfLE hV).op).hom
    (unitSection U)) = (F.obj.map (homOfLE hV).op).hom (((sectionDesc F U s).hom.app (op U)).hom (unitSection U)) at hnat
  rw [hnat, sectionDesc_unitSection]

/-- **the canonical map** `ρ : j_!ℤ_W ⟶ j_!ℤ_U` for `W ≤ U` (the morphism corresponding to the restriction to
`W` of the unit section of `j_!ℤ_U`) -/
def restrictExtend {W : Opens X} (h : W ≤ U) : extendByZeroConstant W ⟶ extendByZeroConstant U :=
  sectionDesc (extendByZeroConstant U) W (((extendByZeroConstant U).obj.map (homOfLE h).op).hom (unitSection U))

theorem restrictExtend_unitSection {W : Opens X} (h : W ≤ U) :
    ((restrictExtend U h).hom.app (op W)).hom (unitSection W) =
      ((extendByZeroConstant U).obj.map (homOfLE h).op).hom (unitSection U) :=
  sectionDesc_unitSection _ _ _

/-- `ρ` sends the constant section `z` over `V ≤ W` to the constant section `z` over `V` -/
theorem restrictExtend_extendConstSec {W : Opens X} (h : W ≤ U) {V : Opens X} (hV : V ≤ W) (z : ℤ) :
    ((restrictExtend U h).hom.app (op V)).hom (extendConstSec W hV z) = extendConstSec U (le_trans hV h) z := by
  unfold restrictExtend
  rw [sectionDesc_extendConstSec, map_comp_hom_apply, unitSection_eq, extendConstSec_res,
    zsmul_extendConstSec_one]

/-- **an open cover gives a jointly epimorphic family**: if `U ≤ ⨆ W_i` with `W_i ≤ U`, the canonical maps
`j_!ℤ_{W_i} ⟶ j_!ℤ_U` are jointly epimorphic -/
theorem isJointlyEpi_restrictExtend {ι : Type u} (W : ι → Opens X) (hW : ∀ i, W i ≤ U) (hcover : U ≤ iSup W) :
    IsJointlyEpi (fun i => restrictExtend U (hW i)) := by
  intro T g h hgh
  apply hom_ext_of_unitSection
  refine TopCat.Sheaf.eq_of_locally_eq' T W U (fun i => homOfLE (hW i)) hcover _ _ fun i => ?_
  have key : ∀ (φ : extendByZeroConstant U ⟶ T),
      (T.obj.map (homOfLE (hW i)).op).hom ((φ.hom.app (op U)).hom (unitSection U)) =
        ((restrictExtend U (hW i) ≫ φ).hom.app (op (W i))).hom (unitSection (W i)) := by
    intro φ
    have hnat := congrArg (fun g => g.hom (unitSection U)) (φ.hom.naturality (homOfLE (hW i)).op)
    change (φ.hom.app (op (W i))).hom (((extendByZeroConstant U).obj.map (homOfLE (hW i)).op).hom (unitSection U)) =
      (T.obj.map (homOfLE (hW i)).op).hom ((φ.hom.app (op U)).hom (unitSection U)) at hnat
    rw [← hnat, ← restrictExtend_unitSection]
    rfl
  rw [key g, key h, hgh i]

end TopCat.Sheaf

end
