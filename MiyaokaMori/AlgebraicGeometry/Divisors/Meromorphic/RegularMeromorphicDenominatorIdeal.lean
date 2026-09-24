import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RegularMeromorphicSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleStalkFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame

/-! # The ideal of denominators of a regular meromorphic section

Construction part of Stacks 02P0 (`divisors-lemma-regular-meromorphic-ideal-denominators`). `s` is a regular
meromorphic section of the line bundle `L`, given by its local fraction representation
`s|_{U i} = num i / den i` (`RegularMeromorphicSection`).

* `IsMul s V g l` ("`l = g • s` on `V`"): on every open `W ≤ V ⊓ U i`, `den i • l = g • num i`.
  - `IsMul.unique`: `l` is unique (`den i` acts injectively on sections of `L`, `den_smul_eq_zero`: its germs
    are non-zero-divisors and the stalks of a line bundle are free);
  - `IsMul.of_single`: it suffices to check the identity in one chart `V ≤ U i` (transfer to the other charts
    by the compatibility `den j • num i = den i • num j` and the injectivity of `den i`).
* `denomIdeal s : X.Modules`, the ideal of denominators `I ⊆ O_X`, `I(V) = {g | ∃ l, IsMul s V g l}`, built as
  a `PresheafOfModules.Submodule` of the unit module; the sheaf condition glues the (unique) witnesses in `L`.
* `denomInclusion s : I ⟶ O_X` (the map `a = 1`), a monomorphism; `mulHom s : I ⟶ L` (the map `b = s`,
  `g ↦ g • s`), a monomorphism (`b(g) = 0 ⟹ g • num i = 0 ⟹ g = 0` by the regularity of `num i` on stalks).
* `den_smul_mulHom_app` (clause 8 of `exists_denominatorIdeal`): `den i • b(h) = a(h) • num i` on `V ≤ U i`;
  `exists_app_eq_of_den_smul` (clause 9): `den i • l = g • num i` on `V ≤ U i` implies `g ∈ I(V)`.

Quasi-coherence of `I` and the nowhere-dense set `T` containing the supports of the cokernels are in the
sibling modules `RegularMeromorphicDenominatorIdealQuasicoherent` and
`RegularMeromorphicDenominatorCokernelSupport`; the assembly is `Stacks02p0`.

`toRing` is the identity `Γ(O_X, V) → Γ(X, V)`; it only fixes the *inferred* type of a section of the unit module
(the two are definitionally equal, but `rw` needs the syntactic form `Γ(X, V)`).

Source: Stacks 02P0 (statement and first paragraph of the proof), 02OX.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection

variable {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} [L.IsLineBundle]
  (s : AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection L)

/-- Germs and scalar multiplication commute (Mathlib `PresheafOfModules.germ_smul`). -/
theorem germ_smul'' (M : X.Modules) {V : X.Opens} {y : X} (hy : y ∈ V) (r : Γ(X, V)) (m : Γ(M, V)) :
    M.presheaf.germ V y hy (r • m) = X.presheaf.germ V y hy r • M.presheaf.germ V y hy m :=
  PresheafOfModules.germ_smul (R := X.presheaf) M.val y V hy r m

/-- Restricting twice in `O_X` is restricting once. -/
theorem resX_resX {A B C : X.Opens} (h1 : A ≤ B) (h2 : B ≤ C) (r : Γ(X, C)) :
    X.presheaf.map (homOfLE h1).op (X.presheaf.map (homOfLE h2).op r) =
      X.presheaf.map (homOfLE (h1.trans h2)).op r := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]; rfl

/-- Restricting twice in a module sheaf is restricting once. -/
theorem resM_resM (M : X.Modules) {A B C : X.Opens} (h1 : A ≤ B) (h2 : B ≤ C) (m : Γ(M, C)) :
    M.presheaf.map (homOfLE h1).op (M.presheaf.map (homOfLE h2).op m) =
      M.presheaf.map (homOfLE (h1.trans h2)).op m := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]; rfl

/-- The germ of `den i` restricted to any smaller open is still a non-zero-divisor. -/
theorem germ_den_res_mem_nonZeroDivisors (i : s.ι) {W : X.Opens} (hW : W ≤ s.U i) (x : X)
    (hx : x ∈ W) :
    X.presheaf.germ W x hx (X.presheaf.map (homOfLE hW).op (s.den i)) ∈
      nonZeroDivisors (X.presheaf.stalk x) := by
  rw [X.presheaf.germ_res_apply]
  exact s.den_mem_nonZeroDivisors i x (hW hx)

/-- **Multiplication by `den i` is injective on sections of `L`** over opens inside `U i`: the germ of
`den i` is a non-zero-divisor and the stalks of the line bundle `L` are free, hence torsion-free. -/
theorem den_smul_eq_zero (i : s.ι) {W : X.Opens} (hW : W ≤ s.U i) (l : Γ(L, W))
    (h : X.presheaf.map (homOfLE hW).op (s.den i) • l = 0) : l = 0 := by
  refine TopCat.Presheaf.section_ext (⟨L.presheaf, L.isSheaf⟩ : TopCat.Sheaf Ab X) W l 0
    fun x hx => ?_
  have h1 := congrArg (L.presheaf.germ W x hx) h
  rw [map_zero] at h1 ⊢
  rw [germ_smul''] at h1
  have hreg : IsRegular (X.presheaf.germ W x hx (X.presheaf.map (homOfLE hW).op (s.den i))) :=
    isRegular_iff_mem_nonZeroDivisors.mpr (s.germ_den_res_mem_nonZeroDivisors i hW x hx)
  have := AlgebraicGeometry.Scheme.Modules.free_stalk_of_isLineBundle L x
  have h2 : X.presheaf.germ W x hx (X.presheaf.map (homOfLE hW).op (s.den i)) •
      L.presheaf.germ W x hx l =
      X.presheaf.germ W x hx (X.presheaf.map (homOfLE hW).op (s.den i)) •
        (0 : L.presheaf.stalk x) := by
    rw [smul_zero]; exact h1
  exact hreg.isSMulRegular (M := L.presheaf.stalk x) h2

/-- `IsMul s V g l`: "`l = g • s` on `V`", i.e. on every open `W ≤ V` inside some `U i`,
`den i • l = g • num i`. -/
def IsMul (V : X.Opens) (g : Γ(X, V)) (l : Γ(L, V)) : Prop :=
  ∀ (i : s.ι) (W : X.Opens) (hWV : W ≤ V) (hWU : W ≤ s.U i),
    X.presheaf.map (homOfLE hWU).op (s.den i) • L.presheaf.map (homOfLE hWV).op l =
      X.presheaf.map (homOfLE hWV).op g • L.presheaf.map (homOfLE hWU).op (s.num i)

theorem IsMul.zero (V : X.Opens) : s.IsMul V 0 0 := by
  intro i W hWV hWU
  rw [map_zero, map_zero, smul_zero, zero_smul]

variable {s}

theorem IsMul.add {V : X.Opens} {g g' : Γ(X, V)} {l l' : Γ(L, V)} (h : s.IsMul V g l)
    (h' : s.IsMul V g' l') : s.IsMul V (g + g') (l + l') := by
  intro i W hWV hWU
  rw [map_add, map_add, smul_add, add_smul, h i W hWV hWU, h' i W hWV hWU]

theorem IsMul.smul {V : X.Opens} {g : Γ(X, V)} {l : Γ(L, V)} (h : s.IsMul V g l) (r : Γ(X, V)) :
    s.IsMul V (r * g) (r • l) := by
  intro i W hWV hWU
  rw [map_mul, Scheme.Modules.map_smul, smul_comm, h i W hWV hWU, mul_smul]

theorem IsMul.res {V : X.Opens} {g : Γ(X, V)} {l : Γ(L, V)} (h : s.IsMul V g l) {V' : X.Opens}
    (hV' : V' ≤ V) :
    s.IsMul V' (X.presheaf.map (homOfLE hV').op g) (L.presheaf.map (homOfLE hV').op l) := by
  intro i W hWV hWU
  have e1 : L.presheaf.map (homOfLE hWV).op (L.presheaf.map (homOfLE hV').op l) =
      L.presheaf.map (homOfLE (hWV.trans hV')).op l := by
    rw [← ConcreteCategory.comp_apply, ← L.presheaf.map_comp]; rfl
  have e2 : X.presheaf.map (homOfLE hWV).op (X.presheaf.map (homOfLE hV').op g) =
      X.presheaf.map (homOfLE (hWV.trans hV')).op g := by
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]; rfl
  rw [e1, e2]
  exact h i W (hWV.trans hV') hWU

/-- Sections of `L` over `V` agreeing on every `V ⊓ U i` are equal (the `U i` cover `X`). -/
theorem section_ext_cover (V : X.Opens) (l l' : Γ(L, V))
    (h : ∀ i, L.presheaf.map (homOfLE (inf_le_left : V ⊓ s.U i ≤ V)).op l =
      L.presheaf.map (homOfLE (inf_le_left : V ⊓ s.U i ≤ V)).op l') : l = l' := by
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨L.presheaf, L.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i => V ⊓ s.U i) V (fun i => homOfLE inf_le_left) ?_ l l' h
  intro x hx
  obtain ⟨i, hi⟩ := s.cover x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩

/-- Sections of `O_X` over `V` agreeing on every `V ⊓ U i` are equal. -/
theorem ring_section_ext_cover (V : X.Opens) (g g' : Γ(X, V))
    (h : ∀ i, X.presheaf.map (homOfLE (inf_le_left : V ⊓ s.U i ≤ V)).op g =
      X.presheaf.map (homOfLE (inf_le_left : V ⊓ s.U i ≤ V)).op g') : g = g' := by
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun i => V ⊓ s.U i) V (fun i => homOfLE inf_le_left) ?_ g g' h
  intro x hx
  obtain ⟨i, hi⟩ := s.cover x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩

/-- **Uniqueness of `g • s`**: two sections `l`, `l'` of `L` with `l = g • s = l'` coincide. -/
theorem IsMul.unique {V : X.Opens} {g : Γ(X, V)} {l l' : Γ(L, V)} (h : s.IsMul V g l)
    (h' : s.IsMul V g l') : l = l' := by
  refine s.section_ext_cover V l l' fun i => ?_
  have hz : X.presheaf.map (homOfLE (inf_le_right : V ⊓ s.U i ≤ s.U i)).op (s.den i) •
      (L.presheaf.map (homOfLE (inf_le_left : V ⊓ s.U i ≤ V)).op l -
        L.presheaf.map (homOfLE (inf_le_left : V ⊓ s.U i ≤ V)).op l') = 0 := by
    rw [smul_sub, h i _ inf_le_left inf_le_right, h' i _ inf_le_left inf_le_right, sub_self]
  exact sub_eq_zero.mp (s.den_smul_eq_zero i inf_le_right _ hz)

variable (s)

/-- **Transfer from one chart to all**: if `den i • l = g • num i` on `V ≤ U i`, then `l = g • s`
on `V` (on every `W ≤ V ⊓ U j`, `den j • l = g • num j`), using the compatibility
`den j • num i = den i • num j` and the injectivity of `den i`. -/
theorem IsMul.of_single (i : s.ι) {V : X.Opens} (hV : V ≤ s.U i) {g : Γ(X, V)} {l : Γ(L, V)}
    (h : X.presheaf.map (homOfLE hV).op (s.den i) • l = g • L.presheaf.map (homOfLE hV).op (s.num i)) :
    s.IsMul V g l := by
  intro j W hWV hWU
  have hWi : W ≤ s.U i := hWV.trans hV
  -- restrict the hypothesis to `W`
  have hW : X.presheaf.map (homOfLE hWi).op (s.den i) • L.presheaf.map (homOfLE hWV).op l =
      X.presheaf.map (homOfLE hWV).op g • L.presheaf.map (homOfLE hWi).op (s.num i) := by
    have := congrArg (L.presheaf.map (homOfLE hWV).op) h
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply,
      ← X.presheaf.map_comp, ← ConcreteCategory.comp_apply, ← L.presheaf.map_comp] at this
    exact this
  -- restrict the compatibility to `W`
  have hc : X.presheaf.map (homOfLE hWU).op (s.den j) • L.presheaf.map (homOfLE hWi).op (s.num i) =
      X.presheaf.map (homOfLE hWi).op (s.den i) • L.presheaf.map (homOfLE hWU).op (s.num j) := by
    have hle : W ≤ s.U i ⊓ s.U j := le_inf hWi hWU
    have := congrArg (L.presheaf.map (homOfLE hle).op) (s.compat i j)
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply,
      ← X.presheaf.map_comp, ← ConcreteCategory.comp_apply, ← L.presheaf.map_comp,
      ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, ← ConcreteCategory.comp_apply,
      ← L.presheaf.map_comp] at this
    exact this
  -- `den i • (den j • l - g • num j) = 0`
  have hz : X.presheaf.map (homOfLE hWi).op (s.den i) •
      (X.presheaf.map (homOfLE hWU).op (s.den j) • L.presheaf.map (homOfLE hWV).op l -
        X.presheaf.map (homOfLE hWV).op g • L.presheaf.map (homOfLE hWU).op (s.num j)) = 0 := by
    rw [smul_sub, smul_comm (X.presheaf.map (homOfLE hWi).op (s.den i))
      (X.presheaf.map (homOfLE hWU).op (s.den j)), hW,
      smul_comm (X.presheaf.map (homOfLE hWU).op (s.den j)) (X.presheaf.map (homOfLE hWV).op g), hc,
      smul_comm (X.presheaf.map (homOfLE hWi).op (s.den i)) (X.presheaf.map (homOfLE hWV).op g),
      sub_self]
  exact sub_eq_zero.mp (s.den_smul_eq_zero i hWi _ hz)

/-! ## The ideal of denominators as a subsheaf of `O_X` -/

/-- A section of the unit module `O_X` viewed as a section of the structure sheaf
(`Γ(O_X, V) = Γ(X, V)` definitionally; this wrapper fixes the inferred type). -/
def toRing {V : X.Opens} (g : Γ(unitModule X, V)) : Γ(X, V) := g

theorem toRing_zero (V : X.Opens) : toRing (0 : Γ(unitModule X, V)) = 0 := rfl

theorem toRing_add {V : X.Opens} (g g' : Γ(unitModule X, V)) : toRing (g + g') = toRing g + toRing g' :=
  rfl

theorem toRing_smul {V : X.Opens} (r : Γ(X, V)) (g : Γ(unitModule X, V)) :
    toRing (r • g) = r * toRing g := rfl

theorem toRing_map {V W : X.Opens} (hWV : W ≤ V) (g : Γ(unitModule X, V)) :
    toRing ((unitModule X).presheaf.map (homOfLE hWV).op g) = X.presheaf.map (homOfLE hWV).op (toRing g) :=
  rfl

theorem toRing_injective (V : X.Opens) : Function.Injective (toRing (X := X) (V := V)) := fun _ _ h => h

/-- Sections of the ideal of denominators over `V`: those `g ∈ O_X(V)` for which `g • s` is a section
of `L` over `V` (i.e. some `l ∈ L(V)` satisfies `den i • l = g • num i` on all `W ≤ V ⊓ U i`). -/
def denomSections (V : X.Opens) : Submodule Γ(X, V) Γ(unitModule X, V) where
  carrier := {g | ∃ l : Γ(L, V), s.IsMul V (toRing g) l}
  zero_mem' := ⟨0, IsMul.zero s V⟩
  add_mem' := by
    rintro g g' ⟨l, hl⟩ ⟨l', hl'⟩
    exact ⟨l + l', hl.add hl'⟩
  smul_mem' := by
    rintro r g ⟨l, hl⟩
    exact ⟨r • l, hl.smul r⟩

theorem mem_denomSections_iff (V : X.Opens) (g : Γ(unitModule X, V)) :
    g ∈ s.denomSections V ↔ ∃ l : Γ(L, V), s.IsMul V (toRing g) l := Iff.rfl

/-- The ideal of denominators as a sub-presheaf of modules of `O_X`. -/
def denomSubmodule : (unitModule X).val.Submodule where
  obj V := s.denomSections V.unop
  map {V W} f := by
    rintro g ⟨l, hl⟩
    exact ⟨L.presheaf.map f l, hl.res f.unop.le⟩

/-- The sheaf condition for the ideal of denominators: gluing takes place in `O_X`; the witnesses
`l_j = g_j • s` are compatible by uniqueness (`IsMul.unique`) and glue in `L` to a witness for the glued
section. -/
theorem denomSubmodule_isSheaf :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      s.denomSubmodule.toPresheafOfModules.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι V sf hsf
  have hcompat : (unitModule X).presheaf.IsCompatible V (fun j ↦ (sf j).val) := by
    intro j k
    exact congrArg Subtype.val (hsf j k)
  obtain ⟨g, hg, hunique⟩ :=
    (show (unitModule X).presheaf.IsSheaf from (unitModule X).isSheaf).isSheafUniqueGluing V
      (fun j ↦ (sf j).val) hcompat
  -- the witnesses on the pieces
  have hw : ∀ j, ∃ l : Γ(L, V j), s.IsMul (V j) (toRing (sf j).val) l := fun j => (sf j).property
  choose lf hlf using hw
  have hgj : ∀ j, X.presheaf.map (homOfLE (le_iSup V j)).op (toRing g) = toRing (sf j).val :=
    fun j => congrArg toRing (hg j)
  have hlcompat : L.presheaf.IsCompatible V lf := by
    intro j k
    refine IsMul.unique (g := X.presheaf.map (Opens.infLELeft (V j) (V k)).op (toRing (sf j).val))
      ((hlf j).res (Opens.infLELeft (V j) (V k)).le) ?_
    have hgg : X.presheaf.map (Opens.infLELeft (V j) (V k)).op (toRing (sf j).val) =
        X.presheaf.map (Opens.infLERight (V j) (V k)).op (toRing (sf k).val) :=
      congrArg toRing (hcompat j k)
    rw [hgg]
    exact (hlf k).res (Opens.infLERight (V j) (V k)).le
  obtain ⟨l, hl, -⟩ :=
    (show L.presheaf.IsSheaf from L.isSheaf).isSheafUniqueGluing V lf hlcompat
  have hgmem : g ∈ s.denomSections (iSup V) := by
    refine ⟨l, ?_⟩
    intro i W hWV hWU
    -- check the identity locally on the pieces `W ⊓ V j`
    refine TopCat.Sheaf.eq_of_locally_eq' (⟨L.presheaf, L.isSheaf⟩ : TopCat.Sheaf Ab X)
      (fun j => W ⊓ V j) W (fun j => homOfLE inf_le_left) ?_ _ _ fun j => ?_
    · intro x hx
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hWV hx)
      exact Opens.mem_iSup.mpr ⟨j, hx, hj⟩
    · have h1 := (hlf j) i (W ⊓ V j) inf_le_right (inf_le_left.trans hWU)
      rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul]
      have e1 : L.presheaf.map (homOfLE (inf_le_left : W ⊓ V j ≤ W)).op
          (L.presheaf.map (homOfLE hWV).op l) =
          L.presheaf.map (homOfLE (inf_le_right : W ⊓ V j ≤ V j)).op (lf j) := by
        have hlj : L.presheaf.map (homOfLE (le_iSup V j)).op l = lf j := hl j
        rw [← hlj, resM_resM, resM_resM]
      have e2 : X.presheaf.map (homOfLE (inf_le_left : W ⊓ V j ≤ W)).op
          (X.presheaf.map (homOfLE hWV).op (toRing g)) =
          X.presheaf.map (homOfLE (inf_le_right : W ⊓ V j ≤ V j)).op (toRing (sf j).val) := by
        rw [← hgj j, resX_resX, resX_resX]
      rw [e1, e2, resX_resX, resM_resM]
      exact h1
  refine ⟨⟨g, hgmem⟩, ?_, ?_⟩
  · intro j
    apply Subtype.ext
    exact hg j
  · intro t ht
    apply Subtype.ext
    apply hunique t.val
    intro j
    exact congrArg Subtype.val (ht j)

/-- **The ideal of denominators `I ⊆ O_X`** of the regular meromorphic section `s` (Stacks 02P0). -/
def denomIdeal : X.Modules where
  val := s.denomSubmodule.toPresheafOfModules
  isSheaf := s.denomSubmodule_isSheaf

/-- The inclusion `a = (1 : I → O_X)`. -/
def denomInclusion : s.denomIdeal ⟶ unitModule X := ⟨s.denomSubmodule.ι⟩

instance mono_denomInclusion : CategoryTheory.Mono s.denomInclusion where
  right_cancellation f g h := by
    apply SheafOfModules.Hom.ext
    apply (CategoryTheory.cancel_mono s.denomSubmodule.ι).mp
    exact congrArg SheafOfModules.Hom.val h

theorem denomInclusion_app (V : X.Opens) (h : Γ(s.denomIdeal, V)) :
    s.denomInclusion.app V h = h.val := rfl

/-- The witness `g • s ∈ L(V)` for `g ∈ I(V)` (unique by `IsMul.unique`). -/
def mulSection {V : X.Opens} (h : Γ(s.denomIdeal, V)) : Γ(L, V) :=
  Classical.choose h.property

theorem mulSection_spec {V : X.Opens} (h : Γ(s.denomIdeal, V)) :
    s.IsMul V (toRing h.val) (s.mulSection h) :=
  Classical.choose_spec h.property

theorem mulSection_eq {V : X.Opens} (h : Γ(s.denomIdeal, V)) {l : Γ(L, V)}
    (hl : s.IsMul V (toRing h.val) l) : s.mulSection h = l :=
  (s.mulSection_spec h).unique hl

theorem mulSection_add {V : X.Opens} (h h' : Γ(s.denomIdeal, V)) :
    s.mulSection (h + h') = s.mulSection h + s.mulSection h' :=
  s.mulSection_eq _ ((s.mulSection_spec h).add (s.mulSection_spec h'))

theorem mulSection_smul {V : X.Opens} (r : Γ(X, V)) (h : Γ(s.denomIdeal, V)) :
    s.mulSection (r • h) = r • s.mulSection h :=
  s.mulSection_eq _ ((s.mulSection_spec h).smul r)

theorem mulSection_res {V W : X.Opens} (hWV : W ≤ V) (h : Γ(s.denomIdeal, V)) :
    s.mulSection (s.denomIdeal.presheaf.map (homOfLE hWV).op h) =
      L.presheaf.map (homOfLE hWV).op (s.mulSection h) :=
  s.mulSection_eq _ ((s.mulSection_spec h).res hWV)

/-- **The map `b = (s : I → L)`**, `g ↦ g • s`. -/
def mulHom : s.denomIdeal ⟶ L :=
  ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun h => s.mulSection h
          map_zero' := s.mulSection_eq 0 (IsMul.zero s V.unop)
          map_add' := s.mulSection_add }
      naturality := fun {V W} f => by
        ext h
        change s.mulSection (s.denomIdeal.presheaf.map f h) = L.presheaf.map f (s.mulSection h)
        exact s.mulSection_res f.unop.le h }
    (fun V r h => s.mulSection_smul r h)⟩

theorem mulHom_app {V : X.Opens} (h : Γ(s.denomIdeal, V)) : s.mulHom.app V h = s.mulSection h := rfl

/-- **Clause 8 of the statement**: on `V ≤ U i`, `den i • b(h) = a(h) • num i`. -/
theorem den_smul_mulHom_app (i : s.ι) {V : X.Opens} (hV : V ≤ s.U i) (h : Γ(s.denomIdeal, V)) :
    X.presheaf.map (homOfLE hV).op (s.den i) • s.mulHom.app V h =
      toRing (s.denomInclusion.app V h) • L.presheaf.map (homOfLE hV).op (s.num i) := by
  have := s.mulSection_spec h i V le_rfl hV
  rw [mulHom_app, denomInclusion_app]
  have e1 : L.presheaf.map (homOfLE (le_refl V)).op (s.mulSection h) = s.mulSection h := by
    rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from rfl, L.presheaf.map_id]; rfl
  have e2 : X.presheaf.map (homOfLE (le_refl V)).op (toRing h.val) = toRing h.val := by
    rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from rfl, X.presheaf.map_id]; rfl
  rw [e1, e2] at this
  exact this

/-- **Clause 9 of the statement**: on `V ≤ U i`, if `den i • l = g • num i` for some `l ∈ L(V)`
then `g ∈ I(V)`. -/
theorem exists_app_eq_of_den_smul (i : s.ι) {V : X.Opens} (hV : V ≤ s.U i) (g : Γ(X, V))
    (hg : ∃ l : Γ(L, V), X.presheaf.map (homOfLE hV).op (s.den i) • l =
      g • L.presheaf.map (homOfLE hV).op (s.num i)) :
    ∃ h : Γ(s.denomIdeal, V), toRing (s.denomInclusion.app V h) = g := by
  obtain ⟨l, hl⟩ := hg
  exact ⟨⟨g, l, IsMul.of_single s i hV hl⟩, rfl⟩

/-- Sections in `I` are determined by their image in `O_X` (`a` is injective on sections). -/
theorem denomInclusion_app_injective (V : X.Opens) : Function.Injective (s.denomInclusion.app V) :=
  fun _ _ h => Subtype.ext h

/-- `b` is injective on sections: if `g • s = 0` then `g • num i = 0` on every `V ⊓ U i`, hence `g = 0`
on every `V ⊓ U i` by the regularity of `num i` on stalks, hence `g = 0`. -/
theorem mulHom_app_injective (V : X.Opens) : Function.Injective (s.mulHom.app V) := by
  intro h h' hh
  rw [mulHom_app, mulHom_app] at hh
  suffices hz : ∀ h : Γ(s.denomIdeal, V), s.mulSection h = 0 → h = 0 by
    have := hz (h - h') (by rw [sub_eq_add_neg, s.mulSection_add, ← neg_one_smul (R := Γ(X, V)) h',
      s.mulSection_smul, hh, neg_one_smul, add_neg_cancel])
    exact sub_eq_zero.mp this
  intro h hh0
  apply Subtype.ext
  apply toRing_injective
  change toRing h.val = 0
  have h1 : ∀ i, X.presheaf.map (homOfLE (inf_le_right : V ⊓ s.U i ≤ s.U i)).op (s.den i) •
      L.presheaf.map (homOfLE (inf_le_left : V ⊓ s.U i ≤ V)).op (s.mulSection h) =
      X.presheaf.map (homOfLE (inf_le_left : V ⊓ s.U i ≤ V)).op (toRing h.val) •
        L.presheaf.map (homOfLE (inf_le_right : V ⊓ s.U i ≤ s.U i)).op (s.num i) :=
    fun i => s.mulSection_spec h i (V ⊓ s.U i) inf_le_left inf_le_right
  generalize toRing h.val = g at h1 ⊢
  refine s.ring_section_ext_cover V g 0 fun i => ?_
  rw [map_zero]
  have h1i := h1 i
  rw [hh0, map_zero, smul_zero] at h1i
  refine TopCat.Presheaf.section_ext X.sheaf (V ⊓ s.U i) _ 0 fun x hx => ?_
  change X.presheaf.germ (V ⊓ s.U i) x hx
    (X.presheaf.map (homOfLE (inf_le_left : V ⊓ s.U i ≤ V)).op g) = X.presheaf.germ (V ⊓ s.U i) x hx 0
  rw [map_zero]
  have h2 := congrArg (L.presheaf.germ (V ⊓ s.U i) x hx) h1i
  rw [map_zero, germ_smul''] at h2
  have hnum := s.num_regular i x ((inf_le_right : V ⊓ s.U i ≤ s.U i) hx)
    (X.presheaf.germ (V ⊓ s.U i) x hx
      (X.presheaf.map (homOfLE (inf_le_left : V ⊓ s.U i ≤ V)).op g))
  apply hnum
  rw [← L.presheaf.germ_res_apply (homOfLE (inf_le_right : V ⊓ s.U i ≤ s.U i)) x hx (s.num i)]
  exact h2.symm

/-- A morphism of `O_X`-modules injective on all sections is a monomorphism (same proof as
`SectionRestrictionSequenceAux.mono_of_injective_app`, repeated here to keep the import closure small). -/
theorem mono_of_injective_app' {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.Opens, Function.Injective (φ.app U)) : CategoryTheory.Mono φ := by
  have hloc : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun U => h U.unop)
  have : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    Sheaf.mono_of_isLocallyInjective _
  exact (SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map this

/-- `b : I ⟶ L` is a monomorphism. -/
instance mono_mulHom : CategoryTheory.Mono s.mulHom :=
  mono_of_injective_app' _ s.mulHom_app_injective

end AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection

end
