import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcApproxGoodOn

/-! # Gluing two good sub-presheaves along their overlap

Support module for `QcFiniteTypeApproxFiniteSections` (Stacks 01PD, the gluing step of the
induction).

Let `F` be a quasi-coherent module on a quasi-separated scheme `S`, `G` good on the quasi-compact open `U`,
`G''` good on the quasi-compact open `W`, and suppose `G` and `G''` have the same sections on every open
`V ≤ U ⊓ W`. The glued sub-presheaf `glue F G G'' U W` has as sections over `U'` those `t ∈ F(U')` with
`t|_{U' ⊓ U} ∈ G` and `t|_{U' ⊓ W} ∈ G''`. Then

* `glue_obj_eq_left` / `glue_obj_eq_right`: on opens `≤ U` (resp. `≤ W`) it agrees with `G` (resp. `G''`);
* `GoodOn.glue`: it is good on `U ⊔ W`. Locality and finite type are inherited; the localization property
  and saturation on an affine `U'' ≤ U ⊔ W` follow from `exists_pow_smul_eq_map_basicOpen` for `F` and the
  saturation of `G` and `G''` over the quasi-compact intersections `U'' ⊓ U`, `U'' ⊓ W`
  (`GoodOn.exists_pow_smul_map_inf_mem`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.QcApprox

variable {S : AlgebraicGeometry.Scheme.{u}} (F : S.Modules)

/-- The glued sub-presheaf of `F`: sections over `U'` whose restrictions to `U' ⊓ U` lie in `G` and whose
restrictions to `U' ⊓ W` lie in `G''`. -/
def glue (G G'' : F.val.Submodule) (U W : S.Opens) : F.val.Submodule where
  obj U' := (G.obj (op (U'.unop ⊓ U))).comap
      (F.val.restrictₛₗ (homOfLE (inf_le_left : U'.unop ⊓ U ≤ U'.unop)).op) ⊓
    (G''.obj (op (U'.unop ⊓ W))).comap
      (F.val.restrictₛₗ (homOfLE (inf_le_left : U'.unop ⊓ W ≤ U'.unop)).op)
  map {U' V'} f := by
    rintro t ⟨h1, h2⟩
    obtain ⟨t', rfl⟩ : ∃ t' : Γ(F, U'.unop), t' = t := ⟨t, rfl⟩
    have hle : V'.unop ≤ U'.unop := leOfHom f.unop
    have h1' : F.presheaf.map (homOfLE (inf_le_left : U'.unop ⊓ U ≤ U'.unop)).op t' ∈
      objΓ G (U'.unop ⊓ U) := h1
    have h2' : F.presheaf.map (homOfLE (inf_le_left : U'.unop ⊓ W ≤ U'.unop)).op t' ∈
      objΓ G'' (U'.unop ⊓ W) := h2
    refine ⟨?_, ?_⟩
    · change F.presheaf.map (homOfLE inf_le_left).op (F.presheaf.map (homOfLE hle).op t') ∈
        objΓ G (V'.unop ⊓ U)
      rw [map_map]
      have := mem_map_of_mem G (inf_le_inf_right U hle) h1'
      rwa [map_map] at this
    · change F.presheaf.map (homOfLE inf_le_left).op (F.presheaf.map (homOfLE hle).op t') ∈
        objΓ G'' (V'.unop ⊓ W)
      rw [map_map]
      have := mem_map_of_mem G'' (inf_le_inf_right W hle) h2'
      rwa [map_map] at this

theorem mem_glue_iff (G G'' : F.val.Submodule) (U W U' : S.Opens) (t : Γ(F, U')) :
    t ∈ objΓ (glue F G G'' U W) U' ↔
      F.presheaf.map (homOfLE (inf_le_left : U' ⊓ U ≤ U')).op t ∈ objΓ G (U' ⊓ U) ∧
      F.presheaf.map (homOfLE (inf_le_left : U' ⊓ W ≤ U')).op t ∈ objΓ G'' (U' ⊓ W) :=
  Iff.rfl

variable {F}

/-- On opens `U' ≤ U` the glued sub-presheaf is `G` (using that `G = G''` on opens `≤ U ⊓ W`). -/
theorem glue_obj_eq_left {G G'' : F.val.Submodule} {U W : S.Opens}
    (hagree : ∀ V ≤ U ⊓ W, objΓ G V = objΓ G'' V) {U' : S.Opens} (hU' : U' ≤ U) :
    objΓ (glue F G G'' U W) U' = objΓ G U' := by
  ext t
  rw [mem_glue_iff]
  constructor
  · rintro ⟨h1, -⟩
    exact (mem_iff_map_mem_of_le_of_le G inf_le_left (le_inf le_rfl hU') t).mpr h1
  · intro ht
    refine ⟨mem_map_of_mem G _ ht, ?_⟩
    rw [← hagree (U' ⊓ W) (inf_le_inf_right W hU')]
    exact mem_map_of_mem G _ ht

/-- On opens `U' ≤ W` the glued sub-presheaf is `G''`. -/
theorem glue_obj_eq_right {G G'' : F.val.Submodule} {U W : S.Opens}
    (hagree : ∀ V ≤ U ⊓ W, objΓ G V = objΓ G'' V) {U' : S.Opens} (hU' : U' ≤ W) :
    objΓ (glue F G G'' U W) U' = objΓ G'' U' := by
  ext t
  rw [mem_glue_iff]
  constructor
  · rintro ⟨-, h2⟩
    exact (mem_iff_map_mem_of_le_of_le G'' inf_le_left (le_inf le_rfl hU') t).mpr h2
  · intro ht
    refine ⟨?_, mem_map_of_mem G'' _ ht⟩
    rw [hagree (U' ⊓ U) (le_inf inf_le_right (inf_le_left.trans hU'))]
    exact mem_map_of_mem G'' _ ht

/-- Restricting a section of `F` over an affine `U''` to `D(h) ⊓ U`, from its restriction to `D(h)`. -/
private theorem map_inf_of_map {U'' U : S.Opens} (h : Γ(S, U'')) (t : Γ(F, U'')) :
    F.presheaf.map (homOfLE (inf_le_left.trans (S.basicOpen_le h) : S.basicOpen h ⊓ U ≤ U'')).op t =
      F.presheaf.map (homOfLE (inf_le_left : S.basicOpen h ⊓ U ≤ S.basicOpen h)).op
        (F.presheaf.map (homOfLE (S.basicOpen_le h)).op t) := by
  rw [map_map]

/-- **Gluing preserves goodness** (Stacks 01PD, the induction step). -/
theorem GoodOn.glue [QuasiSeparatedSpace S] [F.IsQuasicoherent] {G G'' : F.val.Submodule}
    {U W : S.Opens} (hG : GoodOn F G U) (hG'' : GoodOn F G'' W) (hU : IsCompact (U : Set S))
    (hW : IsCompact (W : Set S)) (hagree : ∀ V ≤ U ⊓ W, objΓ G V = objΓ G'' V) :
    GoodOn F (glue F G G'' U W) (U ⊔ W) where
  mem_of_locally U' _ t ht := by
    rw [mem_glue_iff]
    constructor
    · apply hG.mem_of_locally _ inf_le_right
      intro x hx
      obtain ⟨U₀, h₀, hx₀, ht₀⟩ := ht x hx.1
      refine ⟨U₀ ⊓ U, inf_le_inf_right U h₀, ⟨hx₀, hx.2⟩, ?_⟩
      rw [map_map]
      have := ((mem_glue_iff F G G'' U W U₀ _).mp ht₀).1
      rwa [map_map] at this
    · apply hG''.mem_of_locally _ inf_le_right
      intro x hx
      obtain ⟨U₀, h₀, hx₀, ht₀⟩ := ht x hx.1
      refine ⟨U₀ ⊓ W, inf_le_inf_right W h₀, ⟨hx₀, hx.2⟩, ?_⟩
      rw [map_map]
      have := ((mem_glue_iff F G G'' U W U₀ _).mp ht₀).2
      rwa [map_map] at this
  exists_pow_smul_eq_map U'' _ haff h s hs := by
    obtain ⟨n, t, ht⟩ := F.exists_pow_smul_eq_map_basicOpen haff h s
    rw [mem_glue_iff] at hs
    have h1 : F.presheaf.map (homOfLE (inf_le_left.trans (S.basicOpen_le h) :
        S.basicOpen h ⊓ U ≤ U'')).op t ∈ objΓ G (S.basicOpen h ⊓ U) := by
      rw [map_inf_of_map, ht, AlgebraicGeometry.Scheme.Modules.map_smul]
      exact Submodule.smul_mem _ _ hs.1
    have h2 : F.presheaf.map (homOfLE (inf_le_left.trans (S.basicOpen_le h) :
        S.basicOpen h ⊓ W ≤ U'')).op t ∈ objΓ G'' (S.basicOpen h ⊓ W) := by
      rw [map_inf_of_map, ht, AlgebraicGeometry.Scheme.Modules.map_smul]
      exact Submodule.smul_mem _ _ hs.2
    obtain ⟨m₁, hm₁⟩ := hG.exists_pow_smul_map_inf_mem hU haff h t h1
    obtain ⟨m₂, hm₂⟩ := hG''.exists_pow_smul_map_inf_mem hW haff h t h2
    refine ⟨m₁ + m₂ + n, h ^ (m₁ + m₂) • t, ?_, ?_⟩
    · rw [mem_glue_iff]
      constructor
      · rw [add_comm m₁ m₂, pow_add, mul_smul, AlgebraicGeometry.Scheme.Modules.map_smul]
        exact Submodule.smul_mem _ _ hm₁
      · rw [pow_add, mul_smul, AlgebraicGeometry.Scheme.Modules.map_smul]
        exact Submodule.smul_mem _ _ hm₂
    · rw [AlgebraicGeometry.Scheme.Modules.map_smul, ht, map_pow, smul_smul, ← pow_add]
  exists_pow_smul_mem U'' _ haff h t ht := by
    rw [mem_glue_iff] at ht
    have h1 : F.presheaf.map (homOfLE (inf_le_left.trans (S.basicOpen_le h) :
        S.basicOpen h ⊓ U ≤ U'')).op t ∈ objΓ G (S.basicOpen h ⊓ U) := by
      rw [map_inf_of_map]; exact ht.1
    have h2 : F.presheaf.map (homOfLE (inf_le_left.trans (S.basicOpen_le h) :
        S.basicOpen h ⊓ W ≤ U'')).op t ∈ objΓ G'' (S.basicOpen h ⊓ W) := by
      rw [map_inf_of_map]; exact ht.2
    obtain ⟨m₁, hm₁⟩ := hG.exists_pow_smul_map_inf_mem hU haff h t h1
    obtain ⟨m₂, hm₂⟩ := hG''.exists_pow_smul_map_inf_mem hW haff h t h2
    refine ⟨m₁ + m₂, ?_⟩
    rw [mem_glue_iff]
    constructor
    · rw [add_comm m₁ m₂, pow_add, mul_smul, AlgebraicGeometry.Scheme.Modules.map_smul]
      exact Submodule.smul_mem _ _ hm₁
    · rw [pow_add, mul_smul, AlgebraicGeometry.Scheme.Modules.map_smul]
      exact Submodule.smul_mem _ _ hm₂
  exists_affine_fg x hx := by
    rcases (Opens.mem_sup).mp hx with hxU | hxW
    · obtain ⟨U'', haff, hxU'', hle, p, g, hg⟩ := hG.exists_affine_fg x hxU
      exact ⟨U'', haff, hxU'', hle.trans le_sup_left, p, g, (glue_obj_eq_left hagree hle).trans hg⟩
    · obtain ⟨U'', haff, hxU'', hle, p, g, hg⟩ := hG''.exists_affine_fg x hxW
      exact ⟨U'', haff, hxU'', hle.trans le_sup_right, p, g, (glue_obj_eq_right hagree hle).trans hg⟩

end AlgebraicGeometry.Scheme.Modules.QcApprox

end
