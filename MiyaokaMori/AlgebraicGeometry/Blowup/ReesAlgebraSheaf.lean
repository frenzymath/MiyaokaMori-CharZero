import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
-- The next two imports are not used by this file; downstream modules rely on them transitively.
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentOfAffineLocalizing
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.CoproductSectionsLocallyFinite
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # The Rees algebra of an ideal sheaf

The grading of the Rees algebra `⊕_{n ≥ 0} Iⁿ` of an ideal of a commutative ring, and the Rees
algebra of an ideal sheaf `I` on a scheme `X` as a graded quasi-coherent `O_X`-algebra `⊕ Iⁿ`
(with `I⁰ = O_X`), the algebra whose relative Proj is the blowup of `X` along `I` (Stacks 01OG).

The `n`-th piece `Iⁿ` is realised as the subsheaf `I.powSubmodule n` of `O_X` whose sections over `U`
are the functions whose restriction to every affine open `V ≤ U` lies in `I(V)ⁿ`. Locality of this
condition is obtained from Mathlib's `IdealSheafData.map_ideal` / `ideal_le_comap_ideal` for an
arbitrary inclusion of affine opens, applied to the ideal sheaf `I ^ n` (`ideal_pow` is `rfl`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- Ring theory: the `n`-th graded piece of the Rees algebra `reesAlgebra I ⊆ R[X]`, namely `Iⁿ·Xⁿ`. -/
noncomputable def Ideal.reesGrading {R : Type u} [CommRing R] (I : Ideal R) :
    ℕ → Submodule R (reesAlgebra I) :=
  MiyaokaMori.RingTheory.ReesAlgebra.grading I

noncomputable instance {R : Type u} [CommRing R] (I : Ideal R) : GradedAlgebra (Ideal.reesGrading I) :=
  MiyaokaMori.RingTheory.ReesAlgebra.gradedAlgebra I

/-- The affine blowup algebra `R[I/a] ⊆ R_a`. -/
noncomputable def Ideal.affineBlowup {R : Type u} [CommRing R] (I : Ideal R) (a : R) :
    Subalgebra R (Localization.Away a) :=
  MiyaokaMori.RingTheory.IdealFractionChart.chart I a

/-- The `n`-th power `Iⁿ` of an ideal sheaf as a subsheaf of modules of `O_X`: a section over `U` belongs
to it iff its restriction to every affine open `V ≤ U` lies in `I(V)ⁿ`. -/
def AlgebraicGeometry.Scheme.IdealSheafData.powSubmodule {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) : (SheafOfModules.unit X.ringCatSheaf).val.Submodule where
  obj U :=
    { carrier := { s | ∀ V : X.affineOpens, ∀ h : (V : X.Opens) ≤ U.unop,
        (X.presheaf.map (CategoryTheory.homOfLE h).op s : Γ(X, (V : X.Opens))) ∈ (I.ideal V) ^ n }
      zero_mem' := fun V h =>
        (Ideal.comap (X.presheaf.map (CategoryTheory.homOfLE h).op).hom ((I.ideal V) ^ n)).zero_mem
      add_mem' := fun {_ _} ha hb V h =>
        (Ideal.comap (X.presheaf.map (CategoryTheory.homOfLE h).op).hom ((I.ideal V) ^ n)).add_mem
          (ha V h) (hb V h)
      smul_mem' := fun c {_} hs V h =>
        Ideal.mul_mem_left
          (Ideal.comap (X.presheaf.map (CategoryTheory.homOfLE h).op).hom ((I.ideal V) ^ n)) c
          (hs V h) }
  map := fun {U U'} f s hs V h => by
    have hU : (V : X.Opens) ≤ U.unop := h.trans (CategoryTheory.leOfHom f.unop)
    have := hs V hU
    convert this using 1
    change (X.presheaf.map f ≫ X.presheaf.map (CategoryTheory.homOfLE h).op) s = _
    rw [← X.presheaf.map_comp]; rfl

/-! ### Locality of membership in `J.ideal V` (Mathlib `IdealSheafData`)

Mathlib has `IdealSheafData.map_ideal` / `ideal_le_comap_ideal` for an arbitrary inclusion of affine
opens `U ≤ V` (not only basic opens). The two lemmas below are the "membership in `J.ideal V` is local"
statement shared by `powSubmodule_isSheaf`, `powMulToUnit_mem` and `reesAlgebra_sections`; they are
proved for any ideal sheaf `J` and then applied to `J := I ^ n` (Mathlib's `Pow X.IdealSheafData ℕ`,
`ideal_pow` is `rfl`). -/

/-- Restricting twice is restricting once (the composite of two `homOfLE`s is a `homOfLE`). -/
theorem AlgebraicGeometry.Scheme.presheaf_map_homOfLE_map_homOfLE {X : AlgebraicGeometry.Scheme.{u}}
    {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (CategoryTheory.homOfLE h₂).op (X.presheaf.map (CategoryTheory.homOfLE h₁).op s) =
      X.presheaf.map (CategoryTheory.homOfLE (h₂.trans h₁)).op s := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]; rfl

/-- Membership in `J.ideal V` (`V` affine) can be checked on the basic opens `D(r)`, `r ∈ s`, of a
set `s ⊆ Γ(X, V)` generating the unit ideal: `Γ(X, D(r))` is the localization of `Γ(X, V)` at `r`
(`IsAffineOpen.isLocalization_basicOpen`), `J.ideal (D(r)) = (J.ideal V)·Γ(X, D(r))`
(`IdealSheafData.map_ideal_basicOpen`), and membership in a submodule can be checked after
localizing at a family generating the unit ideal (Mathlib `Submodule.mem_of_isLocalized_span`).
Same argument as Mathlib's `IdealSheafData.le_of_iSup_eq_top`, elementwise. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.mem_ideal_of_span_eq_top {X : AlgebraicGeometry.Scheme.{u}}
    (J : X.IdealSheafData) (V : X.affineOpens) (s : Set Γ(X, (V : X.Opens)))
    (hs : Ideal.span s = ⊤) (x : Γ(X, (V : X.Opens)))
    (hx : ∀ r : s, X.presheaf.map (CategoryTheory.homOfLE (X.basicOpen_le r.1)).op x ∈
      J.ideal (X.affineBasicOpen r.1)) :
    x ∈ J.ideal V := by
  have inst := V.2.isLocalization_basicOpen
  refine Submodule.mem_of_isLocalized_span s hs (fun r : s => Γ(X, X.basicOpen r.1))
    (fun r : s => Algebra.linearMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen r.1)) ?_
  intro r
  simp only [← Submodule.restrictScalars_localized' Γ(X, X.basicOpen r.1),
    Ideal.localized'_eq_map, RingHom.algebraMap_toAlgebra, Submodule.restrictScalars_mem,
    Algebra.linearMap_apply]
  rw [J.map_ideal_basicOpen]
  exact hx r

/-- Locality on an affine open `V`: if every point `p ∈ V` has a basic open `D(f) ∋ p` of `V` with
`x|_{D(f)} ∈ J.ideal (D(f))`, then `x ∈ J.ideal V` (the `f`'s generate the unit ideal because the
`D(f)` cover `V`: `IsAffineOpen.self_le_iSup_basicOpen_iff`). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.mem_ideal_of_forall_exists_basicOpen
    {X : AlgebraicGeometry.Scheme.{u}} (J : X.IdealSheafData) (V : X.affineOpens)
    (x : Γ(X, (V : X.Opens)))
    (h : ∀ p : (V : X.Opens), ∃ f : Γ(X, (V : X.Opens)), (p : X) ∈ X.basicOpen f ∧
      X.presheaf.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op x ∈ J.ideal (X.affineBasicOpen f)) :
    x ∈ J.ideal V := by
  choose f hf hfx using h
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    exact fun p hp => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, ⟨p, hp⟩, rfl⟩, hf ⟨p, hp⟩⟩
  refine J.mem_ideal_of_span_eq_top V (Set.range f) hspan x ?_
  rintro ⟨_, p, rfl⟩
  exact hfx p

/-- **Membership in `I.powSubmodule n` is local.** If `U ≤ ⨆ i, W i` with `W i ≤ U`, and
`s|_{W i} ∈ Γ(W i, Iⁿ)` for every `i`, then `s ∈ Γ(U, Iⁿ)`. Proof: for an affine `V ≤ U` and
`p ∈ V`, pick `i` with `p ∈ W i` and a basic open `D(f) ⊆ V ⊓ W i` of `V` containing `p`
(`IsAffineOpen.exists_basicOpen_le`); `D(f)` is an affine open `≤ W i`, so
`s|_{D(f)} ∈ I(D(f))ⁿ` by the hypothesis on `W i`, and `mem_ideal_of_forall_exists_basicOpen`
applied to the ideal sheaf `I ^ n` gives `s|_V ∈ I(V)ⁿ`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.mem_powSubmodule_of_iSup {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {ι : Type*} (U : X.Opens) (W : ι → X.Opens)
    (hWU : ∀ i, W i ≤ U) (hcov : U ≤ ⨆ i, W i) (s : Γ(X, U))
    (hs : ∀ i, X.presheaf.map (CategoryTheory.homOfLE (hWU i)).op s ∈
      (I.powSubmodule n).obj (Opposite.op (W i))) :
    s ∈ (I.powSubmodule n).obj (Opposite.op U) := by
  intro V hV
  change X.presheaf.map (CategoryTheory.homOfLE hV).op s ∈ (I ^ n).ideal V
  refine (I ^ n).mem_ideal_of_forall_exists_basicOpen V _ ?_
  rintro ⟨p, hp⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov (hV hp))
  obtain ⟨f, hfle, hpf⟩ := V.2.exists_basicOpen_le (V := (V : X.Opens) ⊓ W i) ⟨p, hp, hi⟩ hp
  refine ⟨f, hpf, ?_⟩
  have hle : (X.affineBasicOpen f : X.Opens) ≤ W i := hfle.trans inf_le_right
  have := hs i (X.affineBasicOpen f) hle
  change X.presheaf.map (CategoryTheory.homOfLE hle).op
    (X.presheaf.map (CategoryTheory.homOfLE (hWU i)).op s) ∈ (I.ideal (X.affineBasicOpen f)) ^ n at this
  rw [AlgebraicGeometry.Scheme.presheaf_map_homOfLE_map_homOfLE] at this
  change X.presheaf.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op
    (X.presheaf.map (CategoryTheory.homOfLE hV).op s) ∈ (I.ideal (X.affineBasicOpen f)) ^ n
  rw [AlgebraicGeometry.Scheme.presheaf_map_homOfLE_map_homOfLE]
  exact this

/-- **On an affine open `U`, `Γ(U, Iⁿ) = I(U)ⁿ`.** (⊆) take `V = U`; (⊇) Mathlib's
`IdealSheafData.ideal_le_comap_ideal` for the ideal sheaf `I ^ n` and the affine inclusion `V ≤ U`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.mem_powSubmodule_iff_of_isAffineOpen
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (U : X.affineOpens)
    (s : Γ(X, (U : X.Opens))) :
    s ∈ (I.powSubmodule n).obj (Opposite.op (U : X.Opens)) ↔ s ∈ (I.ideal U) ^ n := by
  constructor
  · intro hs
    have := hs U le_rfl
    rwa [show (CategoryTheory.homOfLE (le_refl (U : X.Opens))).op = 𝟙 _ from rfl,
      X.presheaf.map_id, CommRingCat.id_apply] at this
  · intro hs V hV
    exact Ideal.mem_comap.mp ((I ^ n).ideal_le_comap_ideal (U := V) (V := U) hV hs)

/-- The presheaf underlying `powSubmodule n` is a sheaf (Stacks 01OG; the standard argument that the
powers of an ideal sheaf form sheaves, cf. Stacks 01LA).

Proof: glue in `O_X` to a section `s`; then `s ∈ P(⨆ Uᵢ)` by the locality lemma
`mem_powSubmodule_of_iSup` (since `s|_{Uᵢ} = sᵢ ∈ P(Uᵢ)`); separatedness is inherited from the
injection `P(U) ↪ O_X(U)`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.powSubmodule_isSheaf {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (I.powSubmodule n).toPresheafOfModules.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U sf hsf
  have hcompat : TopCat.Presheaf.IsCompatible (SheafOfModules.unit X.ringCatSheaf).val.presheaf U
      (fun i ↦ (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hunique⟩ :=
    TopCat.Presheaf.IsSheaf.isSheafUniqueGluing
      (show TopCat.Presheaf.IsSheaf (SheafOfModules.unit X.ringCatSheaf).val.presheaf from
        (SheafOfModules.unit X.ringCatSheaf).isSheaf) U (fun i ↦ (sf i).val) hcompat
  have hsP : s ∈ (I.powSubmodule n).obj (Opposite.op (iSup U)) := by
    refine I.mem_powSubmodule_of_iSup n (iSup U) U (le_iSup U) le_rfl s fun i => ?_
    have h := hs i
    change X.presheaf.map (CategoryTheory.homOfLE (le_iSup U i)).op s = (sf i).val at h
    rw [h]
    exact (sf i).property
  refine ⟨⟨s, hsP⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hs i
  · intro t ht
    apply Subtype.ext
    apply hunique t.val
    intro i
    exact congrArg Subtype.val (ht i)

/-- The `n`-th power `Iⁿ` of an ideal sheaf as a sheaf of `O_X`-modules. -/
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.pow {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) : X.Modules where
  val := (I.powSubmodule n).toPresheafOfModules
  isSheaf := I.powSubmodule_isSheaf n

/-- The inclusion `Iⁿ ↪ O_X`. -/
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.powι {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) : I.pow n ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ⟨(I.powSubmodule n).ι⟩

/-- Factoring through `Iⁿ ↪ O_X`: when the values of `g : A ⟶ O_X` lie in `Iⁿ` (hypothesis `hg`), regard
them open-by-open as sections of `Iⁿ`.

The hypothesis `hg` is necessary: for `X = Spec k`, `I = ⊥`, `n = 1`, `A = O_X`, `g = 𝟙` one has
`g(1) = 1 ∉ I(V)¹ = 0`. -/

noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.liftPow {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {A : X.Modules} (g : A ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hg : ∀ (U : X.Opensᵒᵖ) (x : A.val.obj U), (g.val.app U).hom x ∈ (I.powSubmodule n).obj U) :
    A ⟶ I.pow n :=
  ⟨{ app := fun U => ModuleCat.ofHom
        (LinearMap.codRestrict ((I.powSubmodule n).obj U) (g.val.app U).hom (hg U))
     naturality := fun {U V} f => by
       ext x
       apply Subtype.ext
       exact congrArg (fun φ => φ.hom x) (g.val.naturality f) }⟩

/-- `liftPow` followed by the inclusion `powι` is the original `g` (definitional property of
`LinearMap.codRestrict`). This is the common ingredient of the three algebra axioms
`powMul_one_mul` / `powMul_assoc` / `powMul_comm`: `powι` is a monomorphism, so each of them can be
checked in `O_X` after post-composing with `powι`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.liftPow_powι {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {A : X.Modules} (g : A ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hg : ∀ (U : X.Opensᵒᵖ) (x : A.val.obj U), (g.val.app U).hom x ∈ (I.powSubmodule n).obj U) :
    I.liftPow n g hg ≫ I.powι n = g := rfl

open scoped CategoryTheory.MonoidalCategory in

/-- The unit object of the (localized) monoidal structure on `X.Modules` is the structure sheaf: the unit
of `LocalizedMonoidal` is by construction the target `SheafOfModules.unit` of `ε`, so after unfolding
all definitions the two sides coincide. -/
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso (X : AlgebraicGeometry.Scheme.{u}) :
    𝟙_ X.Modules ≅ SheafOfModules.unit X.ringCatSheaf :=
  CategoryTheory.eqToIso (by with_unfolding_all rfl)

/-- `I⁰ = O_X`: every section lies in `I.powSubmodule 0` (the hypothesis of `liftPow` used for
`reesAlgebra.one`). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.mem_powSubmodule_zero {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (U : X.Opensᵒᵖ) (s : (SheafOfModules.unit X.ringCatSheaf).val.obj U) :
    s ∈ (I.powSubmodule 0).obj U := fun V _ => by
  rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top

open scoped CategoryTheory.MonoidalCategory in

/-- The multiplication of `O_X` restricted to `Iᵐ ⊗ Iⁿ`: `Iᵐ ⊗ Iⁿ → O_X ⊗ O_X ≅ O_X` (left unitor). -/
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.powMulToUnit {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (m n : ℕ) : I.pow m ⊗ I.pow n ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (I.powι m ⊗ₘ I.powι n) ≫
    ((AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv ⊗ₘ
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv) ≫
    (λ_ (𝟙_ X.Modules)).hom ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).hom

open scoped CategoryTheory.MonoidalCategory in

/-! ### `powMulToUnit` on pure tensors

The monoidal unit `𝟙_ X.Modules` is *definitionally* the structure sheaf (`monoidalUnitIso` is
`eqToIso rfl`), so on sections its two directions are the identity and its scalar action is the
ring multiplication (all `with_unfolding_all rfl`). These three are `private` copies of the lemmas
`monoidalUnitIso_hom_app` / `monoidalUnitIso_inv_app` / `smul_monoidalUnit_eq_mul` of
`BlowupIsoAwayFromCenterAffineLeaf` (which imports this file, so the names cannot be reused globally). -/

private theorem monoidalUnitIso_hom_app_aux {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens)
    (x : Γ(𝟙_ X.Modules, U)) :
    (((AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).hom.val.app (Opposite.op U) x :
      Γ(X, U))) = x := by
  with_unfolding_all rfl

private theorem monoidalUnitIso_inv_app_aux {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens)
    (x : Γ(X, U)) :
    (((AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv.val.app (Opposite.op U) x :
      Γ(X, U))) = x := by
  with_unfolding_all rfl

private theorem smul_monoidalUnit_eq_mul_aux {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens)
    (r : Γ(X, U)) (a : Γ(𝟙_ X.Modules, U)) :
    ((r • a : Γ(𝟙_ X.Modules, U)) : Γ(X, U)) = r * (show Γ(X, U) from a) := by
  with_unfolding_all rfl

/-- **`powMulToUnit` on a pure tensor is the product of the underlying sections**:
`a ⊗ b ↦ a·b`. Unwind `powMulToUnit = (powι ⊗ powι) ≫ (ε⁻¹ ⊗ ε⁻¹) ≫ (λ_ 𝟙_).hom ≫ ε` on
`tensorSections a b` with `Modules.tensorHom_tensorSections` (twice),
`Modules.leftUnitor_app_tensorSections` (`r ⊗ a ↦ r • a`) and the three `rfl` lemmas above
(same computation as `coe_reesAlgebra_sectionsGMul` in `BlowupIsoAwayFromCenterAffineLeaf`). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.powMulToUnit_tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (m n : ℕ) (U : X.Opens)
    (a : Γ(I.pow m, U)) (b : Γ(I.pow n, U)) :
    ((I.powMulToUnit m n).val.app (Opposite.op U)
        (AlgebraicGeometry.Scheme.Modules.tensorSections (I.pow m) (I.pow n) U a b) : Γ(X, U)) =
      (show Γ(X, U) from a.1) * (show Γ(X, U) from b.1) := by
  have e1 := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (I.powι m) (I.powι n) U a b
  have e2 := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
    (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv
    (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv U
    ((I.powι m).val.app (Opposite.op U) a) ((I.powι n).val.app (Opposite.op U) b)
  have e3 := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections (𝟙_ X.Modules) U
    ((AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv.val.app (Opposite.op U)
      ((I.powι m).val.app (Opposite.op U) a))
    ((AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv.val.app (Opposite.op U)
      ((I.powι n).val.app (Opposite.op U) b))
  have h1 : (I.powMulToUnit m n).val.app (Opposite.op U)
      (AlgebraicGeometry.Scheme.Modules.tensorSections (I.pow m) (I.pow n) U a b) =
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).hom.val.app (Opposite.op U)
        ((λ_ (𝟙_ X.Modules)).hom.val.app (Opposite.op U)
        (((AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv ⊗ₘ
            (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv).val.app (Opposite.op U)
          ((I.powι m ⊗ₘ I.powι n).val.app (Opposite.op U)
            (AlgebraicGeometry.Scheme.Modules.tensorSections (I.pow m) (I.pow n) U a b)))) := rfl
  rw [h1, e1, e2]
  have e3' : (λ_ (𝟙_ X.Modules)).hom.val.app (Opposite.op U)
      (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) U
        ((AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv.val.app (Opposite.op U)
          ((I.powι m).val.app (Opposite.op U) a))
        ((AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv.val.app (Opposite.op U)
          ((I.powι n).val.app (Opposite.op U) b))) =
      (show Γ(X, U) from (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv.val.app
        (Opposite.op U) ((I.powι m).val.app (Opposite.op U) a)) •
        (show Γ(𝟙_ X.Modules, U) from
          (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv.val.app (Opposite.op U)
            ((I.powι n).val.app (Opposite.op U) b)) := e3
  rw [e3']
  refine (monoidalUnitIso_hom_app_aux U _).trans ?_
  refine (smul_monoidalUnit_eq_mul_aux U _ _).trans ?_
  exact congrArg₂ (fun x y : Γ(X, U) => x * y)
    (monoidalUnitIso_inv_app_aux U ((I.powι m).val.app (Opposite.op U) a))
    (monoidalUnitIso_inv_app_aux U ((I.powι n).val.app (Opposite.op U) b))

/-- The presheaf tensor product `G(I^m) ⊗ G(I^n)` whose sheafification is `I^m ⊗ I^n`. -/
private abbrev preTensor {X : AlgebraicGeometry.Scheme.{u}} (A B : X.Modules) :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  CategoryTheory.MonoidalCategoryStruct.tensorObj
    ((SheafOfModules.forget X.ringCatSheaf ⋙
      _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
    ((SheafOfModules.forget X.ringCatSheaf ⋙
      _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B)

/-- Sections of `A ⊗ B` coming from the presheaf tensor product: `t ↦ sheafifyTensorTo (η t)`;
on `a ⊗ₜ b` this is `tensorSections a b` (by definition). -/
private def tensorFromPre {X : AlgebraicGeometry.Scheme.{u}} (A B : X.Modules) (V : X.Opens)
    (t : (preTensor A B).obj (Opposite.op V)) :
    (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B).val.obj (Opposite.op V) :=
  (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B).val.app (Opposite.op V)
    (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (preTensor A B)).app (Opposite.op V) t)

/-- `powMulToUnit` takes every section of `I^m ⊗ I^n` in the image of `tensorFromPre` into
`Γ(V, I^{m+n})`: induction on the tensor (`TensorProduct.induction_on`); on `a ⊗ₜ b` the value is
`a·b` (`powMulToUnit_tensorSections`) and for an affine `W ≤ V`,
`(ab)|_W = a|_W · b|_W ∈ I(W)^m · I(W)^n = I(W)^{m+n}` (`pow_add`, `Ideal.mul_mem_mul`). -/
private theorem powMulToUnit_tensorFromPre_mem {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (m n : ℕ) (V : X.Opens) (t : (preTensor (I.pow m) (I.pow n)).obj (Opposite.op V)) :
    (I.powMulToUnit m n).val.app (Opposite.op V) (tensorFromPre (I.pow m) (I.pow n) V t) ∈
      (I.powSubmodule (m + n)).obj (Opposite.op V) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    convert Submodule.zero_mem ((I.powSubmodule (m + n)).obj (Opposite.op V)) using 2
    exact (congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans (map_zero _)
  | tmul a b =>
    have hmem : (show Γ(X, V) from a.1) * (show Γ(X, V) from b.1) ∈
        (I.powSubmodule (m + n)).obj (Opposite.op V) := by
      intro W hW
      rw [map_mul, pow_add]
      exact Ideal.mul_mem_mul (a.2 W hW) (b.2 W hW)
    exact (congrArg (fun z : Γ(X, V) => z ∈ (I.powSubmodule (m + n)).obj (Opposite.op V))
      (I.powMulToUnit_tensorSections m n V a b)).mpr hmem
  | add x y hx hy =>
    convert Submodule.add_mem _ hx hy using 2
    exact (congrArg _ ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _))).trans (map_add _ _ _)

/-- `Iᵐ · Iⁿ ⊆ Iᵐ⁺ⁿ`: the multiplication `Iᵐ ⊗ Iⁿ → O_X` takes values in `Iᵐ⁺ⁿ` (the hypothesis of
`liftPow` used for `reesAlgebra.mul`).

Proof sketch:
1. The tensor product in `X.Modules` is the sheafification of the presheaf tensor product
   `P = (Iᵐ).val ⊗ (Iⁿ).val`; let `η : P → (Iᵐ ⊗ Iⁿ).val` be the sheafification unit. On a pure tensor
   `a ⊗ b` the composite `η ≫ powMulToUnit` is the product `a·b ∈ O_X(U)` (`powMulToUnit_tensorSections`).
2. For `a ∈ Iᵐ(U)`, `b ∈ Iⁿ(U)` and an affine open `V ≤ U`, `(ab)|_V = a|_V · b|_V ∈ I(V)ᵐ · I(V)ⁿ = I(V)ᵐ⁺ⁿ`
   (`pow_add`, `Ideal.mul_mem_mul`); pure tensors generate `P(U)` (`TensorProduct.induction_on`), so
   `η ≫ g` takes values in `powSubmodule (m+n)` (`powMulToUnit_tensorFromPre_mem`).
3. Sections of the sheafification locally come from `η` (`exists_sheafification_unit_app_eq_map`): for
   `x ∈ (Iᵐ ⊗ Iⁿ)(U)` there is an open cover `{Uᵢ}` of `U` with `x|_{Uᵢ} = η(tᵢ)`, so
   `g(x)|_{Uᵢ} ∈ Iᵐ⁺ⁿ(Uᵢ)`.
4. Membership in `powSubmodule (m+n)` is local (`mem_powSubmodule_of_iSup`), which gives
   `g(x) ∈ Iᵐ⁺ⁿ(U)`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.powMulToUnit_mem {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (m n : ℕ) (U : X.Opensᵒᵖ) (x : (I.pow m ⊗ I.pow n).val.obj U) :
    ((I.powMulToUnit m n).val.app U).hom x ∈ (I.powSubmodule (m + n)).obj U := by
  obtain ⟨U⟩ := U
  have key : ∀ p : X, p ∈ U → ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
      X.presheaf.map (CategoryTheory.homOfLE hVU).op ((I.powMulToUnit m n).val.app (Opposite.op U) x) ∈
        (I.powSubmodule (m + n)).obj (Opposite.op V) := by
    intro p hp
    obtain ⟨V, hVU, hpV, t, ht⟩ := AlgebraicGeometry.Scheme.Modules.exists_sheafification_unit_app_eq_map
      (preTensor (I.pow m) (I.pow n)) U
      ((AlgebraicGeometry.Scheme.Modules.tensorToSheafify (I.pow m) (I.pow n)).val.app (Opposite.op U) x) p hp
    refine ⟨V, hVU, hpV, ?_⟩
    -- restriction commutes with `powMulToUnit`
    have h1 : X.presheaf.map (CategoryTheory.homOfLE hVU).op
        ((I.powMulToUnit m n).val.app (Opposite.op U) x) =
        (I.powMulToUnit m n).val.app (Opposite.op V)
          ((I.pow m ⊗ I.pow n).val.map (CategoryTheory.homOfLE hVU).op x) :=
      (_root_.PresheafOfModules.naturality_apply (I.powMulToUnit m n).val
        (CategoryTheory.homOfLE hVU).op x).symm
    -- `x|_V` comes from the presheaf tensor product
    have h2 : (I.pow m ⊗ I.pow n).val.map (CategoryTheory.homOfLE hVU).op x =
        tensorFromPre (I.pow m) (I.pow n) V t := by
      unfold tensorFromPre
      rw [ht]
      have h3 := _root_.PresheafOfModules.naturality_apply
        (AlgebraicGeometry.Scheme.Modules.tensorToSheafify (I.pow m) (I.pow n)).val
        (CategoryTheory.homOfLE hVU).op x
      rw [← h3]
      exact (congrArg (fun k => k.val.app (Opposite.op V)
        ((I.pow m ⊗ I.pow n).val.map (CategoryTheory.homOfLE hVU).op x))
        (AlgebraicGeometry.Scheme.Modules.tensorToSheafify_comp_sheafifyTensorTo (I.pow m) (I.pow n))).symm
    rw [h1, h2]
    exact powMulToUnit_tensorFromPre_mem I m n V t
  choose V hVU hpV hmem using key
  exact I.mem_powSubmodule_of_iSup (m + n) U (fun p : U => V p p.2) (fun p => hVU p p.2)
    (fun p hp => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpV p hp⟩) _ (fun p => hmem p p.2)

open scoped CategoryTheory.MonoidalCategory

/- Sheaf theory: `⊕ Iⁿ` as a graded quasi-coherent algebra on `X`. The multiplication
   `Iᵐ ⊗ Iⁿ → Iᵐ⁺ⁿ` is the multiplication of `O_X`, `Iᵐ ⊗ Iⁿ → O_X ⊗ O_X ≅ O_X` (left unitor), which
   lands in `Iᵐ⁺ⁿ`; the unit is `O_X = I⁰`. -/

/-- The multiplication `Iᵐ ⊗ Iⁿ → Iᵐ⁺ⁿ` of the Rees algebra. -/

noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.powMul {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (m n : ℕ) : I.pow m ⊗ I.pow n ⟶ I.pow (m + n) :=
  I.liftPow (m + n) (I.powMulToUnit m n) (I.powMulToUnit_mem m n)

/-- The unit `O_X = I⁰` of the Rees algebra. -/

noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.powOne {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) : 𝟙_ X.Modules ⟶ I.pow 0 :=
  I.liftPow 0 (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).hom
    (fun U x => I.mem_powSubmodule_zero U _)

/-- `Iⁿ` is a quasi-coherent sheaf of `O_X`-modules (Stacks 01OG; the powers of an ideal sheaf are
quasi-coherent, cf. Stacks 01LA/01I8: on an affine open they are determined by the ideal and commute
with localization at basic opens).

Proof: by the criterion `isQuasicoherent_of_affine_localizing`, for an affine open `U` and
`h ∈ Γ(X, U)`:
(a) existence: `Γ(D(h), Iⁿ) = I(D(h))ⁿ = (I(U)ⁿ)·Γ(D(h))` (`mem_powSubmodule_iff_of_isAffineOpen` and
`(I ^ n).map_ideal_basicOpen`), and `IsLocalization.mem_map_algebraMap_iff` gives `hᵏ • s = t|_{D(h)}`
with `t ∈ I(U)ⁿ`;
(b) uniqueness: `IsLocalization.map_eq_zero_iff`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.pow_isQuasicoherent {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) : (I.pow n).IsQuasicoherent := by
  refine AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_affine_localizing (I.pow n) ?_ ?_
  · intro U hU h s
    have := hU.isLocalization_basicOpen h
    have hs : s.1 ∈ ((I ^ n).ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) := by
      rw [RingHom.algebraMap_toAlgebra, (I ^ n).map_ideal_basicOpen ⟨U, hU⟩ h]
      exact (I.mem_powSubmodule_iff_of_isAffineOpen n (X.affineBasicOpen (U := ⟨U, hU⟩) h) s.1).mp s.2
    obtain ⟨⟨t, c⟩, hc⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers h) Γ(X, X.basicOpen h)).mp hs
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
    refine ⟨k, ⟨t.1, (I.mem_powSubmodule_iff_of_isAffineOpen n ⟨U, hU⟩ t.1).mpr t.2⟩, ?_⟩
    apply Subtype.ext
    change X.presheaf.map (CategoryTheory.homOfLE (X.basicOpen_le h)).op t.1 =
      (X.presheaf.map (CategoryTheory.homOfLE (X.basicOpen_le h)).op h) ^ k *
        (show Γ(X, X.basicOpen h) from s.1)
    have hc' : (show Γ(X, X.basicOpen h) from s.1) * algebraMap Γ(X, U) Γ(X, X.basicOpen h) (c : Γ(X, U)) =
        algebraMap Γ(X, U) Γ(X, X.basicOpen h) t.1 := hc
    rw [← hk, map_pow, mul_comm] at hc'
    exact hc'.symm
  · intro U hU h t ht
    have := hU.isLocalization_basicOpen h
    have ht' : algebraMap Γ(X, U) Γ(X, X.basicOpen h) t.1 = 0 := congrArg Subtype.val ht
    obtain ⟨c, hc⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers h) Γ(X, X.basicOpen h) t.1).mp ht'
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
    refine ⟨k, Subtype.ext ?_⟩
    change h ^ k * (show Γ(X, U) from t.1) = 0
    rw [hk]
    exact hc

/-! ### The three algebra axioms

Every morphism into `I.pow n` is determined by its composite with the monomorphism `powι n`
(`hom_ext_powι`); after post-composing with `powι`, the axioms become identities between morphisms
into the structure sheaf that hold in **any** (braided) monoidal category for **any** family of
"inclusions" `ιₖ : Pₖ ⟶ O` and unit `ε : 𝟙_ ≅ O` — proved below at the variable level
(`one_mul_aux` / `assoc_aux` / `comm_aux`) and then instantiated. -/

/-- Two morphisms into `Iⁿ` agree as soon as they agree after the inclusion `Iⁿ ↪ O_X`
(`PresheafOfModules.Submodule.ι` is a monomorphism). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.hom_ext_powι {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {A : X.Modules} {f g : A ⟶ I.pow n}
    (h : f ≫ I.powι n = g ≫ I.powι n) : f = g := by
  apply SheafOfModules.Hom.ext
  apply (CategoryTheory.cancel_mono (I.powSubmodule n).ι).mp
  exact congrArg SheafOfModules.Hom.val h

/-- The transport `eqToHom` along `Iᵃ = Iᵇ` (from `a = b`) is absorbed by the inclusions. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.eqToHom_powι {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg I.pow h) ≫ I.powι b = I.powι a := by
  subst h
  exact Category.id_comp _

/-- `powMul` followed by the inclusion is the multiplication of `O_X` (`liftPow_powι`). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.powMul_powι {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (m n : ℕ) :
    I.powMul m n ≫ I.powι (m + n) = I.powMulToUnit m n := rfl

/-- `powOne` followed by the inclusion is the unit isomorphism (`liftPow_powι`). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.powOne_powι {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) :
    I.powOne ≫ I.powι 0 = (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).hom := rfl

section MonoidalAux

variable {C : Type u'} [CategoryTheory.Category.{v'} C] [CategoryTheory.MonoidalCategory C]

private theorem tensorHom_comp_right_aux {X₁ Y₁ X₂ Y₂ Z₂ : C} (a : X₁ ⟶ Y₁) (x : X₂ ⟶ Y₂) (y : Y₂ ⟶ Z₂) :
    a ⊗ₘ (x ≫ y) = (a ⊗ₘ x) ≫ (Y₁ ◁ y) := by
  rw [← CategoryTheory.MonoidalCategory.id_tensorHom,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

private theorem tensorHom_comp_left_aux {X₁ Y₁ Z₁ X₂ Y₂ : C} (x : X₁ ⟶ Y₁) (y : Y₁ ⟶ Z₁) (c : X₂ ⟶ Y₂) :
    (x ≫ y) ⊗ₘ c = (x ⊗ₘ c) ≫ (y ▷ Y₂) := by
  rw [← CategoryTheory.MonoidalCategory.tensorHom_id,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- Left unit law in `O`: `(e ▷ Pm) ≫ (ι₀ ⊗ ιm) ≫ (ε⁻¹ ⊗ ε⁻¹) ≫ λ ≫ ε = λ ≫ ιm` when `e ≫ ι₀ = ε`
(`tensorHom_comp_tensorHom`, `leftUnitor_naturality`). -/
private theorem one_mul_aux {P₀ Pm O : C} (ε : 𝟙_ C ≅ O)
    (e : 𝟙_ C ⟶ P₀) (ι₀ : P₀ ⟶ O) (ιm : Pm ⟶ O) (he : e ≫ ι₀ = ε.hom) :
    (e ▷ Pm) ≫ (ι₀ ⊗ₘ ιm) ≫ (ε.inv ⊗ₘ ε.inv) ≫ (λ_ (𝟙_ C)).hom ≫ ε.hom = (λ_ Pm).hom ≫ ιm := by
  rw [← CategoryTheory.MonoidalCategory.tensorHom_id,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.id_comp, he, ε.hom_inv_id, CategoryTheory.MonoidalCategory.id_tensorHom,
    ← Category.assoc, CategoryTheory.MonoidalCategory.leftUnitor_naturality,
    Category.assoc, Category.assoc, ε.inv_hom_id, Category.comp_id]

/-- Associativity in `O` (`associator_naturality`, `triangle`, `unitors_equal`). -/
private theorem assoc_aux {Pm Pn Pp Pmn Pnp O : C} (ε : 𝟙_ C ≅ O)
    (ιm : Pm ⟶ O) (ιn : Pn ⟶ O) (ιp : Pp ⟶ O) (ιmn : Pmn ⟶ O) (ιnp : Pnp ⟶ O)
    (μmn : Pm ⊗ Pn ⟶ Pmn) (μnp : Pn ⊗ Pp ⟶ Pnp)
    (hmn : μmn ≫ ιmn = (ιm ⊗ₘ ιn) ≫ (ε.inv ⊗ₘ ε.inv) ≫ (λ_ (𝟙_ C)).hom ≫ ε.hom)
    (hnp : μnp ≫ ιnp = (ιn ⊗ₘ ιp) ≫ (ε.inv ⊗ₘ ε.inv) ≫ (λ_ (𝟙_ C)).hom ≫ ε.hom) :
    (α_ Pm Pn Pp).hom ≫ (Pm ◁ μnp) ≫ (ιm ⊗ₘ ιnp) ≫ (ε.inv ⊗ₘ ε.inv) ≫ (λ_ (𝟙_ C)).hom ≫ ε.hom =
      (μmn ▷ Pp) ≫ (ιmn ⊗ₘ ιp) ≫ (ε.inv ⊗ₘ ε.inv) ≫ (λ_ (𝟙_ C)).hom ≫ ε.hom := by
  have hb : (μnp ≫ ιnp) ≫ ε.inv = ((ιn ≫ ε.inv) ⊗ₘ (ιp ≫ ε.inv)) ≫ (λ_ (𝟙_ C)).hom := by
    rw [hnp]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  have hab : (μmn ≫ ιmn) ≫ ε.inv = ((ιm ≫ ε.inv) ⊗ₘ (ιn ≫ ε.inv)) ≫ (λ_ (𝟙_ C)).hom := by
    rw [hmn]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  set a := ιm ≫ ε.inv
  set b := ιn ≫ ε.inv
  set c := ιp ≫ ε.inv
  have h1 : (Pm ◁ μnp) ≫ (ιm ⊗ₘ ιnp) ≫ (ε.inv ⊗ₘ ε.inv) =
      (a ⊗ₘ (b ⊗ₘ c)) ≫ (𝟙_ C ◁ (λ_ (𝟙_ C)).hom) := by
    rw [← CategoryTheory.MonoidalCategory.id_tensorHom,
      CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
      hb, tensorHom_comp_right_aux]
  have h2 : (μmn ▷ Pp) ≫ (ιmn ⊗ₘ ιp) ≫ (ε.inv ⊗ₘ ε.inv) =
      ((a ⊗ₘ b) ⊗ₘ c) ≫ ((λ_ (𝟙_ C)).hom ▷ 𝟙_ C) := by
    rw [← CategoryTheory.MonoidalCategory.tensorHom_id,
      CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
      hab, tensorHom_comp_left_aux]
  rw [reassoc_of% h1, reassoc_of% h2,
    ← CategoryTheory.MonoidalCategory.associator_naturality_assoc]
  congr 1
  rw [← Category.assoc, CategoryTheory.MonoidalCategory.triangle,
    CategoryTheory.MonoidalCategory.unitors_equal]

/-- Commutativity in `O` (`braiding_naturality`, `braiding_tensorUnit_left`, `unitors_equal`). -/
private theorem comm_aux [CategoryTheory.BraidedCategory C] {Pm Pn O : C} (ε : 𝟙_ C ≅ O)
    (ιm : Pm ⟶ O) (ιn : Pn ⟶ O) :
    (β_ Pm Pn).hom ≫ (ιn ⊗ₘ ιm) ≫ (ε.inv ⊗ₘ ε.inv) ≫ (λ_ (𝟙_ C)).hom ≫ ε.hom =
      (ιm ⊗ₘ ιn) ≫ (ε.inv ⊗ₘ ε.inv) ≫ (λ_ (𝟙_ C)).hom ≫ ε.hom := by
  rw [CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    ← Category.assoc, ← CategoryTheory.BraidedCategory.braiding_naturality,
    Category.assoc, CategoryTheory.braiding_tensorUnit_left,
    CategoryTheory.MonoidalCategory.unitors_equal]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end MonoidalAux

/-- Left unit law of the Rees algebra (`I⁰ = O_X` is the unit; Stacks 01OG).

Proof sketch:
1. Reduce to `O_X`: `powι k` is a monomorphism, so it suffices to check the identity after
   post-composing with `I.powι (0 + m)`; `powMul_powι` gives `powMul a b ≫ powι (a+b) = powMulToUnit a b`,
   `powOne_powι` gives `powOne ≫ powι 0 = (monoidalUnitIso X).hom`, and `eqToHom_powι` absorbs the
   transport `eqToHom (congrArg I.pow (Nat.zero_add m).symm)` (note that `0 + m` is not definitionally
   `m`, so this `eqToHom` cannot be removed by `rfl`).
2. It remains to show `(powOne ▷ I.pow m) ≫ powMulToUnit 0 m = (λ_ (I.pow m)).hom ≫ powι m`.
3. Unfold `powMulToUnit 0 m = (powι 0 ⊗ₘ powι m) ≫ (ε⁻¹ ⊗ₘ ε⁻¹) ≫ (λ_ 𝟙_).hom ≫ ε` with
   `ε = monoidalUnitIso X`; by functoriality of `tensorHom` the left side becomes
   `((powOne ≫ powι 0 ≫ ε.inv) ⊗ₘ (powι m ≫ ε.inv)) ≫ (λ_ 𝟙_).hom ≫ ε.hom`.
4. The first factor is `ε.hom ≫ ε.inv = 𝟙`, so the left side is `(𝟙 ◁ (powι m ≫ ε.inv)) ≫ (λ_ 𝟙_).hom ≫ ε.hom`.
5. Naturality of the left unitor gives `(λ_ (I.pow m)).hom ≫ powι m ≫ ε.inv ≫ ε.hom = (λ_ (I.pow m)).hom ≫ powι m`.
Steps 2–5 are the variable-level lemma `one_mul_aux`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.powMul_one_mul {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (m : ℕ) :
    (I.powOne ▷ I.pow m) ≫ I.powMul 0 m =
      (λ_ (I.pow m)).hom ≫ eqToHom (congrArg I.pow (Nat.zero_add m).symm) := by
  apply I.hom_ext_powι (0 + m)
  -- `rw [Category.assoc]` cannot abstract the motive here, so we reassociate by hand
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine Eq.trans ?_ (congrArg (fun k => (λ_ (I.pow m)).hom ≫ k)
    (I.eqToHom_powι (Nat.zero_add m).symm).symm)
  refine (congrArg (fun k => (I.powOne ▷ I.pow m) ≫ k) (I.powMul_powι 0 m)).trans ?_
  exact one_mul_aux (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X) I.powOne (I.powι 0)
    (I.powι m) I.powOne_powι

/-- Associativity of the Rees algebra (Stacks 01OG).

Proof sketch: as for `powMul_one_mul`. Post-compose with the monomorphism `powι (m+n+p)` and use
`powMul_powι` to turn both sides into composites in `O_X`; after unfolding `powMulToUnit` both sides
are "tensor the three inclusions, pass to `𝟙_ ⊗ 𝟙_ ⊗ 𝟙_` via `ε⁻¹`, and contract with the left unitor
in the two possible bracketings", which agree by `associator_naturality`, `triangle` and
`unitors_equal` (the variable-level lemma `assoc_aux`). The transport
`eqToHom (congrArg I.pow (Nat.add_assoc m n p))` is absorbed by `eqToHom_powι`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.powMul_assoc {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (m n p : ℕ) :
    (α_ (I.pow m) (I.pow n) (I.pow p)).hom ≫ (I.pow m ◁ I.powMul n p) ≫ I.powMul m (n + p) =
      (I.powMul m n ▷ I.pow p) ≫ I.powMul (m + n) p ≫ eqToHom (congrArg I.pow (Nat.add_assoc m n p)) := by
  apply I.hom_ext_powι (m + (n + p))
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine (congrArg (fun k => (α_ (I.pow m) (I.pow n) (I.pow p)).hom ≫ k) (Category.assoc _ _ _)).trans
    (Eq.trans ?_ (congrArg (fun k => (I.powMul m n ▷ I.pow p) ≫ k) (Category.assoc _ _ _)).symm)
  refine Eq.trans ?_ (congrArg (fun k => (I.powMul m n ▷ I.pow p) ≫ I.powMul (m + n) p ≫ k)
    (I.eqToHom_powι (Nat.add_assoc m n p)).symm)
  refine (congrArg (fun k => (α_ (I.pow m) (I.pow n) (I.pow p)).hom ≫ (I.pow m ◁ I.powMul n p) ≫ k)
    (I.powMul_powι m (n + p))).trans
    (Eq.trans ?_ (congrArg (fun k => (I.powMul m n ▷ I.pow p) ≫ k) (I.powMul_powι (m + n) p)).symm)
  exact assoc_aux (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X) (I.powι m) (I.powι n)
    (I.powι p) (I.powι (m + n)) (I.powι (n + p)) (I.powMul m n) (I.powMul n p)
    (I.powMul_powι m n) (I.powMul_powι n p)

/-- Commutativity of the Rees algebra: `Iᵐ · Iⁿ = Iⁿ · Iᵐ` because the multiplication of `O_X` is
commutative (Stacks 01OG).

Proof sketch: post-compose with `powι (n+m)` and absorb `eqToHom (congrArg I.pow (Nat.add_comm m n))`
by `eqToHom_powι`. In `O_X` one has to show
`(β_ (I.pow m) (I.pow n)).hom ≫ powMulToUnit n m = powMulToUnit m n`; unfolding both `powMulToUnit`,
naturality of the braiding (applied to `powι m ≫ ε.inv`, `powι n ≫ ε.inv`) reduces this to
`(β_ 𝟙_ 𝟙_).hom ≫ (λ_ 𝟙_).hom = (λ_ 𝟙_).hom`, and `β_{𝟙,𝟙} = 𝟙` by `braiding_tensorUnit_left` and
`unitors_equal` (the variable-level lemma `comm_aux`). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.powMul_comm {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (m n : ℕ) :
    (β_ (I.pow m) (I.pow n)).hom ≫ I.powMul n m =
      I.powMul m n ≫ eqToHom (congrArg I.pow (Nat.add_comm m n)) := by
  apply I.hom_ext_powι (n + m)
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine Eq.trans ?_ (congrArg (fun k => I.powMul m n ≫ k) (I.eqToHom_powι (Nat.add_comm m n)).symm)
  refine (congrArg (fun k => (β_ (I.pow m) (I.pow n)).hom ≫ k) (I.powMul_powι n m)).trans
    (Eq.trans ?_ (I.powMul_powι m n).symm)
  exact comm_aux (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X) (I.powι m) (I.powι n)

/-- The Rees algebra `⊕_{n ≥ 0} Iⁿ` of an ideal sheaf `I` as a graded quasi-coherent `O_X`-algebra
(Stacks 01OG). -/
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.reesAlgebra {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) : X.GradedQCAlgebra where
  part n := I.pow n
  quasicoherent := I.pow_isQuasicoherent
  mul m n := I.powMul m n
  one := I.powOne
  one_mul := I.powMul_one_mul
  mul_assoc := I.powMul_assoc
  mul_comm := I.powMul_comm

/-- On an affine open `U`, the sections of the `n`-th piece of the Rees algebra are the `n`-th power of
the ideal: `Γ(U, Iⁿ) = I(U)ⁿ` (Stacks 01OG: over an affine `Spec R` the algebra `⊕ Iⁿ` is the Rees
algebra `⊕ Iⁿ ⊆ R[X]`). This is the link with the ring-theoretic grading `Ideal.reesGrading`.

Proof: by definition `Γ(U, I.pow n) = { s ∈ Γ(X, U) | ∀ affine V ≤ U, s|_V ∈ I(V)ⁿ }`. The inclusion
`⊆` is the case `V = U`; for `⊇`, `s ∈ I(U)ⁿ` and an affine open `V ≤ U` give `s|_V ∈ I(V)ⁿ` by
`IdealSheafData.ideal_le_comap_ideal` applied to `I ^ n` (see `mem_powSubmodule_iff_of_isAffineOpen`).
The identity map is then the required equivalence. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.reesAlgebra_sections {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ) :
    Nonempty (((I.reesAlgebra.part n).val.obj (Opposite.op (U : X.Opens)) : Type u) ≃
      ((I.ideal U) ^ n : Ideal Γ(X, (U : X.Opens)))) :=
  ⟨Equiv.subtypeEquivRight fun s => I.mem_powSubmodule_iff_of_isAffineOpen n U s⟩

end
