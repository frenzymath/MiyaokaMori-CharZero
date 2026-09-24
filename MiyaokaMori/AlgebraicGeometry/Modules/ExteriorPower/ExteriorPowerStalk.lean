import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ModuleExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Stalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafificationStalk
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestriction
import MiyaokaMori.Algebra.ExteriorPowerSemilinearMap

/-!
# Exterior powers and module stalks

The sectionwise exterior-power presheaf commutes with taking stalks. Finite tuples
of germs have representatives on one common neighbourhood, and equality of two
such tuples is witnessed after one common refinement. The alternating universal
property then constructs the comparison in both directions, including degree zero.

Sources: Stacks Project, `modules.tex`, `lemma-local-tensor-algebra` and
`lemma-stalk-tensor-algebra`; `algebra.tex`, `lemma-colimit-tensor-algebra`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules
open MiyaokaMori.Algebra

universe u

set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u}) (M : X.PresheafOfModules) (x : X)

local instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- Mathlib already has this instance (the stalk module structure for `PresheafOfModules` over
`CommRingCat`), but synthesizing it requires seeing through the non-reducible `def`
`Scheme.PresheafOfModules`. Fixing it here as a local instance lets the later declarations avoid
`backward.isDefEq.respectTransparency false` (which makes `whnf` blow up in this file, see
`exteriorGermExteriorCocone`). The instance has an explicit unique name: a `local instance` is local
only as an attribute, and the automatic name of an anonymous instance is generated from its type, so
two instances of the same type in different files would collide. -/
local instance exteriorPowerStalkPresheafStalkModule :
    Module ↑(X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x) :=
  inferInstance

/-- A finite tuple of module germs has representatives on one common neighbourhood.
The empty tuple is represented on the whole space. -/
theorem modulePresheafStalk_exists_fin (n : ℕ)
    (v : Fin n → ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.obj (op U)),
      ∀ i, TopCat.Presheaf.germ M.presheaf U x hx (a i) = v i := by
  induction n with
  | zero => exact ⟨⊤, trivial, Fin.elim0, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨U, hxU, a, ha⟩ := ih (fun i ↦ v i.succ)
      obtain ⟨V, hVU, hxV, b, hb⟩ :=
        TopCat.Presheaf.exists_le_germ_eq M.presheaf (v 0) hxU
      refine ⟨V, hxV, Fin.cons b (fun i ↦ M.map (CategoryTheory.homOfLE hVU).op (a i)), ?_⟩
      intro i
      refine Fin.cases hb (fun j ↦ ?_) i
      exact (TopCat.Presheaf.germ_res_apply M.presheaf
        (CategoryTheory.homOfLE hVU) x hxV (a j)).trans (ha j)

/-- Equality of two finite tuples of germs holds on one common neighbourhood. -/
theorem modulePresheafStalk_germ_eq_fin (n : ℕ)
    {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V)
    (a : Fin n → M.obj (op U)) (b : Fin n → M.obj (op V))
    (h : ∀ i, TopCat.Presheaf.germ M.presheaf U x hxU (a i) =
      TopCat.Presheaf.germ M.presheaf V x hxV (b i)) :
    ∃ (W : X.Opens) (_hxW : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V),
      ∀ i, M.map iU.op (a i) = M.map iV.op (b i) := by
  induction n with
  | zero =>
      exact ⟨U ⊓ V, ⟨hxU, hxV⟩, CategoryTheory.homOfLE inf_le_left, CategoryTheory.homOfLE inf_le_right,
        fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨W, hxW, iU, iV, hw⟩ :=
        ih (fun i ↦ a i.succ) (fun i ↦ b i.succ) (fun i ↦ h i.succ)
      obtain ⟨Z, hxZ, jU, jV, hz⟩ :=
        TopCat.Presheaf.germ_eq M.presheaf x hxU hxV (a 0) (b 0) (h 0)
      refine ⟨W ⊓ Z, ⟨hxW, hxZ⟩, CategoryTheory.homOfLE inf_le_left ≫ iU,
        CategoryTheory.homOfLE inf_le_left ≫ iV, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · have hzero := congrArg (M.map (CategoryTheory.homOfLE (inf_le_right : W ⊓ Z ≤ Z)).op) hz
        change M.map (CategoryTheory.homOfLE (inf_le_right : W ⊓ Z ≤ Z)).op (M.map jU.op (a 0)) =
          M.map (CategoryTheory.homOfLE (inf_le_right : W ⊓ Z ≤ Z)).op (M.map jV.op (b 0)) at hzero
        have hu : (CategoryTheory.homOfLE inf_le_right : W ⊓ Z ⟶ Z) ≫ jU =
            (CategoryTheory.homOfLE inf_le_left : W ⊓ Z ⟶ W) ≫ iU := Subsingleton.elim _ _
        have hv : (CategoryTheory.homOfLE inf_le_right : W ⊓ Z ⟶ Z) ≫ jV =
            (CategoryTheory.homOfLE inf_le_left : W ⊓ Z ⟶ W) ≫ iV := Subsingleton.elim _ _
        rw [← hu, ← hv, op_comp, op_comp, M.map_comp_apply, M.map_comp_apply]
        exact hzero
      · rw [op_comp, op_comp, M.map_comp_apply, M.map_comp_apply]
        exact congrArg (M.map (CategoryTheory.homOfLE (inf_le_left : W ⊓ Z ≤ W)).op) (hw j)

variable (n : ℕ)

private theorem exteriorPresheafStalk_germ_mk_eq
    {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V)
    (a : Fin n → M.obj (op U)) (b : Fin n → M.obj (op V))
    (h : ∀ i, TopCat.Presheaf.germ M.presheaf U x hxU (a i) =
      TopCat.Presheaf.germ M.presheaf V x hxV (b i)) :
    TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hxU
        (ModuleCat.exteriorPower.mk a) =
      TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf V x hxV
        (ModuleCat.exteriorPower.mk b) := by
  obtain ⟨W, hxW, iU, iV, hw⟩ :=
    modulePresheafStalk_germ_eq_fin X M x n hxU hxV a b h
  apply TopCat.Presheaf.germ_ext (moduleExteriorPresheaf X M n).presheaf W hxW iU iV
  change exteriorRestriction X M n iU.op (ModuleCat.exteriorPower.mk a) =
    exteriorRestriction X M n iV.op (ModuleCat.exteriorPower.mk b)
  rw [exteriorRestriction_mk, exteriorRestriction_mk]
  exact congrArg ModuleCat.exteriorPower.mk (funext hw)

/-- The germ of the wedge of representatives, independent of the common neighbourhood. -/
def exteriorPresheafStalkWedge
    (v : Fin n → ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) :
    ↑(TopCat.Presheaf.stalk (C := Ab) (moduleExteriorPresheaf X M n).presheaf x) := by
  let U := (modulePresheafStalk_exists_fin X M x n v).choose
  let hx := (modulePresheafStalk_exists_fin X M x n v).choose_spec.choose
  let a := (modulePresheafStalk_exists_fin X M x n v).choose_spec.choose_spec.choose
  exact TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx
    (ModuleCat.exteriorPower.mk a)

/-- The stalk wedge is computed using any tuple of representatives. -/
@[simp]
theorem exteriorPresheafStalkWedge_germ (U : X.Opens) (hx : x ∈ U)
    (a : Fin n → M.obj (op U)) :
    exteriorPresheafStalkWedge X M x n
      (fun i ↦ TopCat.Presheaf.germ M.presheaf U x hx (a i)) =
    TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx
      (ModuleCat.exteriorPower.mk a) := by
  exact exteriorPresheafStalk_germ_mk_eq X M x n _ hx _ a
    (modulePresheafStalk_exists_fin X M x n
      (fun i ↦ TopCat.Presheaf.germ M.presheaf U x hx (a i))).choose_spec.choose_spec.choose_spec

private theorem exteriorPresheafStalkWedge_germ_update [DecidableEq (Fin n)]
    (U : X.Opens) (hx : x ∈ U) (w : Fin n → M.obj (op U))
    (j : Fin n) (a : M.obj (op U)) :
    exteriorPresheafStalkWedge X M x n
      (Function.update (fun i ↦ TopCat.Presheaf.germ M.presheaf U x hx (w i)) j
        (TopCat.Presheaf.germ M.presheaf U x hx a)) =
    TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx
      (ModuleCat.exteriorPower.mk (Function.update w j a)) := by
  have h : Function.update
      (fun i ↦ TopCat.Presheaf.germ M.presheaf U x hx (w i)) j
      (TopCat.Presheaf.germ M.presheaf U x hx a) =
      (fun i ↦ TopCat.Presheaf.germ M.presheaf U x hx (Function.update w j a i)) := by
    funext i
    by_cases hij : i = j <;> simp [hij]
  rw [h, exteriorPresheafStalkWedge_germ]

private theorem modulePresheafStalk_exists_fin_pair
    (v : Fin n → ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
    (a b : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) :
    ∃ (U : X.Opens) (hx : x ∈ U) (w : Fin n → M.obj (op U))
      (a' b' : M.obj (op U)),
      (∀ i, TopCat.Presheaf.germ M.presheaf U x hx (w i) = v i) ∧
      TopCat.Presheaf.germ M.presheaf U x hx a' = a ∧
      TopCat.Presheaf.germ M.presheaf U x hx b' = b := by
  obtain ⟨U, hx, q, hq⟩ :=
    modulePresheafStalk_exists_fin X M x (n + 1 + 1) (Fin.cons a (Fin.cons b v))
  exact ⟨U, hx, fun i ↦ q i.succ.succ, q 0, q (Fin.succ 0),
    fun i ↦ hq i.succ.succ, hq 0, hq (Fin.succ 0)⟩

private theorem modulePresheafStalk_exists_scalar_fin
    (r : X.presheaf.stalk x)
    (v : Fin n → ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) :
    ∃ (U : X.Opens) (hx : x ∈ U) (r' : Γ(X, U)) (w : Fin n → M.obj (op U)),
      X.presheaf.germ U x hx r' = r ∧
      ∀ i, TopCat.Presheaf.germ M.presheaf U x hx (w i) = v i := by
  obtain ⟨U, hxU, w, hw⟩ := modulePresheafStalk_exists_fin X M x n v
  obtain ⟨V, hVU, hxV, r', hr⟩ := X.presheaf.exists_le_germ_eq r hxU
  refine ⟨V, hxV, r', fun i ↦ M.map (CategoryTheory.homOfLE hVU).op (w i), hr, ?_⟩
  intro i
  exact (TopCat.Presheaf.germ_res_apply M.presheaf
    (CategoryTheory.homOfLE hVU) x hxV (w i)).trans (hw i)

/-- The stalk wedge is additive in each coordinate. -/
theorem exteriorPresheafStalkWedge_add [DecidableEq (Fin n)]
    (v : Fin n → ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) (j : Fin n)
    (a b : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) :
    exteriorPresheafStalkWedge X M x n (Function.update v j (a + b)) =
      exteriorPresheafStalkWedge X M x n (Function.update v j a) +
        exteriorPresheafStalkWedge X M x n (Function.update v j b) := by
  obtain ⟨U, hx, w, a', b', hw, ha, hb⟩ :=
    modulePresheafStalk_exists_fin_pair X M x n v a b
  rw [← funext hw, ← ha, ← hb, ← map_add]
  rw [exteriorPresheafStalkWedge_germ_update, exteriorPresheafStalkWedge_germ_update,
    exteriorPresheafStalkWedge_germ_update]
  change TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx
      (exteriorPower.ιMulti Γ(X, U) n (Function.update w j (a' + b'))) = _
  rw [AlternatingMap.map_update_add, map_add]
  rfl

/-- The stalk wedge is linear over the actual local ring in each coordinate. -/
theorem exteriorPresheafStalkWedge_smul [DecidableEq (Fin n)]
    (v : Fin n → ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) (j : Fin n)
    (r : X.presheaf.stalk x)
    (a : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) :
    exteriorPresheafStalkWedge X M x n (Function.update v j (r • a)) =
      r • exteriorPresheafStalkWedge X M x n (Function.update v j a) := by
  obtain ⟨U, hx, r', q, hr, hq⟩ :=
    modulePresheafStalk_exists_scalar_fin X M x (n + 1) r (Fin.cons a v)
  let w : Fin n → M.obj (op U) := fun i ↦ q i.succ
  have hw : (fun i ↦ TopCat.Presheaf.germ M.presheaf U x hx (w i)) = v :=
    funext fun i ↦ hq i.succ
  have ha : TopCat.Presheaf.germ M.presheaf U x hx (q 0) = a := hq 0
  rw [← hw, ← ha, ← hr, ← PresheafOfModules.germ_smul (R := X.presheaf) M]
  rw [exteriorPresheafStalkWedge_germ_update, exteriorPresheafStalkWedge_germ_update]
  change TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx
      (exteriorPower.ιMulti Γ(X, U) n (Function.update w j (r' • q 0))) = _
  rw [AlternatingMap.map_update_smul,
    PresheafOfModules.germ_smul (R := X.presheaf) (moduleExteriorPresheaf X M n)]
  rfl

/-- The stalk wedge vanishes when two distinct coordinates agree. -/
theorem exteriorPresheafStalkWedge_eq_zero
    (v : Fin n → ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
    (i j : Fin n) (h : v i = v j) (hij : i ≠ j) :
    exteriorPresheafStalkWedge X M x n v = 0 := by
  obtain ⟨U, hx, w, hw⟩ := modulePresheafStalk_exists_fin X M x n v
  have hv : (fun k ↦ TopCat.Presheaf.germ M.presheaf U x hx
      (Function.update w j (w i) k)) = v := by
    funext k
    by_cases hk : k = j
    · subst k
      simpa only [Function.update_self] using (hw i).trans h
    · simpa only [Function.update_of_ne hk] using hw k
  rw [← hv, exteriorPresheafStalkWedge_germ]
  change TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx
    (exteriorPower.ιMulti Γ(X, U) n (Function.update w j (w i))) = 0
  rw [(exteriorPower.ιMulti Γ(X, U) n).map_eq_zero_of_eq _
    (by simp only [Function.update_of_ne hij, Function.update_self]) hij, map_zero]

/-- The canonical alternating map from tuples of germs to the exterior-presheaf stalk. -/
def exteriorPresheafStalkAlternating :
    AlternatingMap (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)
      ↑(TopCat.Presheaf.stalk (C := Ab) (moduleExteriorPresheaf X M n).presheaf x)
      (Fin n) where
  toFun := exteriorPresheafStalkWedge X M x n
  map_update_add' := exteriorPresheafStalkWedge_add X M x n
  map_update_smul' := exteriorPresheafStalkWedge_smul X M x n
  map_eq_zero_of_eq' := exteriorPresheafStalkWedge_eq_zero X M x n

/-- The universal property sends a wedge of germs to the germ of a local wedge. -/
def exteriorPresheafStalkFromExterior :
    (⋀[X.presheaf.stalk x]^n ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
      →ₗ[X.presheaf.stalk x]
        ↑(TopCat.Presheaf.stalk (C := Ab) (moduleExteriorPresheaf X M n).presheaf x) :=
  exteriorPower.alternatingMapLinearEquiv (exteriorPresheafStalkAlternating X M x n)

/-- The inverse construction has the original wedge germ formula. -/
@[simp]
theorem exteriorPresheafStalkFromExterior_germ (U : X.Opens) (hx : x ∈ U)
    (a : Fin n → M.obj (op U)) :
    exteriorPresheafStalkFromExterior X M x n
      (exteriorPower.ιMulti (X.presheaf.stalk x) n
        (fun i ↦ TopCat.Presheaf.germ M.presheaf U x hx (a i))) =
    TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx
      (ModuleCat.exteriorPower.mk a) := by
  rw [exteriorPresheafStalkFromExterior, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact exteriorPresheafStalkWedge_germ X M x n U hx a

/-- Taking the germ of every entry defines a semilinear map on exterior powers. -/
def exteriorPresheafGermExterior (U : X.Opens) (hx : x ∈ U) :
    (⋀[Γ(X, U)]^n (M.obj (op U))) →ₛₗ[(X.presheaf.germ U x hx).hom]
      (⋀[X.presheaf.stalk x]^n ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) := by
  let A : (M.obj (op U)).AlternatingMap
      ((ModuleCat.restrictScalars (X.presheaf.germ U x hx).hom).obj
        (ModuleCat.of (X.presheaf.stalk x)
          (⋀[X.presheaf.stalk x]^n
            ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)))) n :=
    { toFun := fun v ↦ exteriorPower.ιMulti (X.presheaf.stalk x) n
        (TopCat.Presheaf.germ M.presheaf U x hx ∘ v)
      map_update_add' := by
        intros
        simp only [Function.comp_update, map_add, AlternatingMap.map_update_add]
      map_update_smul' := by
        intros
        simp only [Function.comp_update, PresheafOfModules.germ_smul (R := X.presheaf),
          AlternatingMap.map_update_smul]
        rfl
      map_eq_zero_of_eq' := fun v i j h hij ↦
        (exteriorPower.ιMulti (X.presheaf.stalk x) n).map_eq_zero_of_eq _
          (congrArg (TopCat.Presheaf.germ M.presheaf U x hx) h) hij }
  exact
    { toFun := ModuleCat.exteriorPower.desc A
      map_add' := map_add _
      map_smul' := fun r a ↦ (ModuleCat.exteriorPower.desc A).hom.map_smul r a }

/-- The local exterior map sends a wedge to the wedge of the original germs. -/
@[simp]
theorem exteriorPresheafGermExterior_mk (U : X.Opens) (hx : x ∈ U)
    (a : Fin n → M.obj (op U)) :
    exteriorPresheafGermExterior X M x n U hx (ModuleCat.exteriorPower.mk a) =
      exteriorPower.ιMulti (X.presheaf.stalk x) n
        (fun i ↦ TopCat.Presheaf.germ M.presheaf U x hx (a i)) :=
  ModuleCat.exteriorPower.desc_mk _ _

private theorem exteriorPower_induction
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
    {k : ℕ} {p : (⋀[R]^k N) → Prop}
    (hmk : ∀ v, p (exteriorPower.ιMulti R k v)) (hzero : p 0)
    (hadd : ∀ a b, p a → p b → p (a + b))
    (hsmul : ∀ (r : R) a, p a → p (r • a)) (a : ⋀[R]^k N) : p a := by
  have ha : a ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R k)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨v, rfl⟩ := ha; exact hmk v
  | zero => exact hzero
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul r a _ ha => exact hsmul r a ha

-- A direct induction on generators at the presheaf level makes `erw`/`rw` blow up in `whnf` under
-- `respectTransparency false`. Instead (as for `semilinear_pairing_ext`), the induction is done in the
-- pure algebra lemma `ExteriorPowerSemilinearMap.semilinear_ext_of_span`, which involves no presheaves;
-- here only additivity, semilinearity and the wedge generators remain, all by term-mode proofs without
-- `rw`/`erw`/`simp`.
/-- Taking germs of exterior sections is compatible with restriction to a smaller open. -/
theorem exteriorPresheafGermExterior_restrict
    {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V) (i : V ⟶ U)
    (a : (moduleExteriorPresheaf X M n).obj (op U)) :
    exteriorPresheafGermExterior X M x n V hxV
        ((moduleExteriorPresheaf X M n).map i.op a) =
      exteriorPresheafGermExterior X M x n U hxU a := by
  refine semilinear_ext_of_span (X.presheaf.germ U x hxU).hom
    (fun a ↦ exteriorPresheafGermExterior X M x n V hxV
        ((moduleExteriorPresheaf X M n).map i.op a))
    (fun a ↦ exteriorPresheafGermExterior X M x n U hxU a)
    ?_ ?_ ?_ ?_ (exteriorPower.ιMulti_span _ n _) ?_ a
  · exact fun p q ↦ (congrArg (exteriorPresheafGermExterior X M x n V hxV)
      (map_add ((moduleExteriorPresheaf X M n).map i.op).hom p q)).trans (map_add _ _ _)
  · intro r p
    refine (congrArg (exteriorPresheafGermExterior X M x n V hxV)
      (PresheafOfModules.map_smul (moduleExteriorPresheaf X M n) i.op r p)).trans ?_
    refine (LinearMap.map_smulₛₗ (exteriorPresheafGermExterior X M x n V hxV) _ _).trans ?_
    exact congrArg (· • _) (X.presheaf.germ_res_apply i x hxV r)
  · exact fun p q ↦ map_add _ p q
  · exact fun r p ↦ LinearMap.map_smulₛₗ (exteriorPresheafGermExterior X M x n U hxU) r p
  · rintro _ ⟨v, rfl⟩
    refine (congrArg (exteriorPresheafGermExterior X M x n V hxV)
      (exteriorRestriction_mk X M n i.op v)).trans ?_
    refine (exteriorPresheafGermExterior_mk X M x n V hxV _).trans ?_
    refine Eq.trans ?_ (exteriorPresheafGermExterior_mk X M x n U hxU v).symm
    exact congrArg (exteriorPower.ιMulti (X.presheaf.stalk x) n)
      (funext fun j ↦ TopCat.Presheaf.germ_res_apply M.presheaf i x hxV (v j))

private theorem exteriorPresheafGermExterior_naturality
    (U V : (OpenNhds x)ᵒᵖ) (f : U ⟶ V)
    (a : (moduleExteriorPresheaf X M n).obj (op U.unop.1)) :
    exteriorPresheafGermExterior X M x n V.unop.1 V.unop.2
        ((moduleExteriorPresheaf X M n).map ((OpenNhds.inclusion x).op.map f) a) =
      exteriorPresheafGermExterior X M x n U.unop.1 U.unop.2 a :=
  exteriorPresheafGermExterior_restrict X M x n U.unop.2 V.unop.2
    ((OpenNhds.inclusion x).map f.unop) a

private def exteriorGermExteriorCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙ (moduleExteriorPresheaf X M n).presheaf) where
  pt := AddCommGrpCat.of
    (⋀[X.presheaf.stalk x]^n ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
  ι.app U := AddCommGrpCat.ofHom
    (exteriorPresheafGermExterior X M x n U.unop.1 U.unop.2).toAddMonoidHom
  ι.naturality U V f := by
    ext a
    exact exteriorPresheafGermExterior_naturality X M x n U V f a

private def exteriorPresheafStalkToExteriorAdd :
    ↑(TopCat.Presheaf.stalk (C := Ab) (moduleExteriorPresheaf X M n).presheaf x) →+
      (⋀[X.presheaf.stalk x]^n ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) :=
  (colimit.desc _ (exteriorGermExteriorCocone X M x n)).hom

private theorem exteriorPresheafStalkToExteriorAdd_germ (U : X.Opens) (hx : x ∈ U)
    (a : (moduleExteriorPresheaf X M n).obj (op U)) :
    exteriorPresheafStalkToExteriorAdd X M x n
      (TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx a) =
      exteriorPresheafGermExterior X M x n U hx a :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (exteriorGermExteriorCocone X M x n) (op ⟨U, hx⟩)) a

/-- Taking the wedge of germs descends to a map linear over the actual local ring. -/
def exteriorPresheafStalkToExterior :
    ↑(TopCat.Presheaf.stalk (C := Ab) (moduleExteriorPresheaf X M n).presheaf x)
      →ₗ[X.presheaf.stalk x]
        (⋀[X.presheaf.stalk x]^n ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) where
  toFun := exteriorPresheafStalkToExteriorAdd X M x n
  map_add' := map_add _
  map_smul' r a := by
    obtain ⟨U, hxU, r', rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, a', rfl⟩ := TopCat.Presheaf.exists_le_germ_eq
      (moduleExteriorPresheaf X M n).presheaf a hxU
    rw [← X.presheaf.germ_res_apply (CategoryTheory.homOfLE hVU) x hxV r']
    erw [← PresheafOfModules.germ_smul (R := X.presheaf)
      (moduleExteriorPresheaf X M n), exteriorPresheafStalkToExteriorAdd_germ,
      exteriorPresheafStalkToExteriorAdd_germ, LinearMap.map_smulₛₗ]
    rfl

/-- The forward comparison preserves every represented wedge generator. -/
@[simp]
theorem exteriorPresheafStalkToExterior_germ_mk (U : X.Opens) (hx : x ∈ U)
    (a : Fin n → M.obj (op U)) :
    exteriorPresheafStalkToExterior X M x n
      (TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx
        (ModuleCat.exteriorPower.mk a)) =
      exteriorPower.ιMulti (X.presheaf.stalk x) n
        (fun i ↦ TopCat.Presheaf.germ M.presheaf U x hx (a i)) := by
  change exteriorPresheafStalkToExteriorAdd X M x n _ = _
  rw [exteriorPresheafStalkToExteriorAdd_germ, exteriorPresheafGermExterior_mk]

/-- The exterior-presheaf stalk is canonically the exterior power of the stalk.
The equivalence is valid for every module presheaf and every natural degree. -/
def exteriorPresheafStalkEquiv :
    ↑(TopCat.Presheaf.stalk (C := Ab) (moduleExteriorPresheaf X M n).presheaf x)
      ≃ₗ[X.presheaf.stalk x]
        (⋀[X.presheaf.stalk x]^n ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x)) :=
  LinearEquiv.ofLinearMap (exteriorPresheafStalkToExterior X M x n)
    (exteriorPresheafStalkFromExterior X M x n)
    (by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      obtain ⟨U, hx, a, ha⟩ := modulePresheafStalk_exists_fin X M x n v
      rw [← funext ha]
      change exteriorPresheafStalkToExterior X M x n
        (exteriorPresheafStalkFromExterior X M x n
          (exteriorPower.ιMulti (X.presheaf.stalk x) n _)) = _
      rw [exteriorPresheafStalkFromExterior_germ, exteriorPresheafStalkToExterior_germ_mk]
      rfl)
    (by
      ext a
      obtain ⟨U, hx, a', rfl⟩ := TopCat.Presheaf.exists_germ_eq
        (moduleExteriorPresheaf X M n).presheaf a
      change exteriorPresheafStalkFromExterior X M x n
          (exteriorPresheafStalkToExterior X M x n
            (TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx a')) =
        TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx a'
      induction a' using exteriorPower_induction with
      | hmk v =>
          erw [exteriorPresheafStalkToExterior_germ_mk,
            exteriorPresheafStalkFromExterior_germ]
          rfl
      | hzero => simp only [map_zero]
      | hadd a b ha hb => simp only [map_add, ha, hb]
      | hsmul r a ha =>
          rw [PresheafOfModules.germ_smul (R := X.presheaf),
            _root_.map_smul, _root_.map_smul, ha])

/-- The canonical presheaf equivalence preserves the original wedge germ. -/
@[simp]
theorem exteriorPresheafStalkEquiv_germ_mk (U : X.Opens) (hx : x ∈ U)
    (a : Fin n → M.obj (op U)) :
    exteriorPresheafStalkEquiv X M x n
      (TopCat.Presheaf.germ (moduleExteriorPresheaf X M n).presheaf U x hx
        (ModuleCat.exteriorPower.mk a)) =
      exteriorPower.ιMulti (X.presheaf.stalk x) n
        (fun i ↦ TopCat.Presheaf.germ M.presheaf U x hx (a i)) :=
  exteriorPresheafStalkToExterior_germ_mk X M x n U hx a

/-- The same bridge as at the beginning of the file, in the spelling `M : X.Modules`
(`M.presheaf.stalk x` goes through `M.val`, a different syntactic shape from the section variable
`M : X.PresheafOfModules`, so instance search cannot reuse it). Explicitly named to avoid collisions
with other files. -/
local instance exteriorPowerStalkModulesStalkModule (X : Scheme.{u}) (M : X.Modules) (x : X) :
    Module ↑(X.presheaf.stalk x) ↑(M.presheaf.stalk x) :=
  inferInstanceAs (Module ↑(X.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk (C := Ab) M.val.presheaf x))

/-- The stalk of the sheafified exterior power is the exterior power of the module stalk. -/
def moduleExteriorPowerStalkEquiv (X : Scheme.{u}) (M : X.Modules) (x : X) (n : ℕ) :
    (moduleExteriorPower X M n).presheaf.stalk x
      ≃ₗ[X.presheaf.stalk x]
      (⋀[X.presheaf.stalk x]^n (M.presheaf.stalk x)) := by
  exact (moduleSheafificationStalkEquiv X (moduleExteriorPresheaf X M.val n) x).symm.trans
    (exteriorPresheafStalkEquiv X M.val x n)

/-- The comparison sends the original sheaf wedge germ to the wedge of the component germs. -/
@[simp]
theorem moduleExteriorPowerStalkEquiv_wedge_germ
    (X : Scheme.{u}) (M : X.Modules) (x : X) (n : ℕ)
    (U : X.Opens) (hx : x ∈ U) (v : Fin n → Γ(M, U)) :
    moduleExteriorPowerStalkEquiv X M x n
      ((moduleExteriorPower X M n).presheaf.germ U x hx
        (moduleExteriorWedge X M n U v)) =
      exteriorPower.ιMulti (X.presheaf.stalk x) n
        (fun i ↦ M.presheaf.germ U x hx (v i)) := by
  rw [moduleExteriorPowerStalkEquiv, LinearEquiv.trans_apply]
  erw [moduleSheafificationStalkEquiv_symm_germ]
  exact exteriorPresheafStalkEquiv_germ_mk X M.val x n U hx v

end AlgebraicGeometry.Scheme.Modules
