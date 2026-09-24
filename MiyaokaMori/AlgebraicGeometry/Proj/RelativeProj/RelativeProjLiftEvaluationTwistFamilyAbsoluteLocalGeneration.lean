import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap

/-! # Sections of a pullback are locally `O`-combinations of pulled-back sections (via stalks)

Helper module for `RelativeProjLiftEvaluationTwistFamilyAbsolute.lean`.

Let `f : Y ⟶ X`, `M : X.Modules`. The stalk of `f^*M` at `t` is `O_{Y,t} ⊗_{O_{X,f t}} M_{f t}`
(`modulePullbackStalkTensorMap_bijective`), and the pure tensor
`r ⊗ germ g` corresponds to `r • germ (η g)` (`modulePullbackStalkTensorMap_tmul`, `modulePullbackStalkUnitAddHom_germ`).
Hence every section `x` of `f^*M` over `B` agrees, near each `t ∈ B`, with a finite sum `Σ r_i • η(g_i)|_{B'}`.

We package this as a **comparison principle** (`SectionMapPair.exists_nhds_res_eq`, `SectionMapPair.eq`): two
families of section maps `c, c' : Γ(f^*M, B) → Γ(Y, B)` which are additive, `Γ(Y, B)`-linear and compatible with
restriction, and which agree near every point on every pulled-back section `η g|_{B'}`, agree everywhere. No
quasi-coherence of `M` is needed (the twisting sheaves of a weighted `Proj` have no such instance in this library). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)

/-- `germ (r • m) = germ r • germ m` for a module sheaf on a scheme. -/
theorem germ_smul_sections {Z : AlgebraicGeometry.Scheme.{u}} (N : Z.Modules) {V : Z.Opens} {y : Z} (hy : y ∈ V)
    (r : Γ(Z, V)) (m : Γ(N, V)) :
    N.presheaf.germ V y hy (r • m) = Z.presheaf.germ V y hy r • N.presheaf.germ V y hy m :=
  PresheafOfModules.germ_smul (R := Z.presheaf) N.val y V hy r m

/-- **A pair of section maps to be compared.** `c, c' : Γ(f^*M, B) → Γ(Y, B)` for every open `B`, both additive,
`Γ(Y, B)`-linear and compatible with restriction, and agreeing *near every point* on every pulled-back section
`η g|_{B'}` (`g ∈ Γ(M, V)`, `B' ≤ f⁻¹V`). -/
structure SectionMapPair (c c' : ∀ B : Y.Opens, Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B) → Γ(Y, B)) :
    Prop where
  add : ∀ (B : Y.Opens) (x y : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B)), c B (x + y) = c B x + c B y
  add' : ∀ (B : Y.Opens) (x y : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B)),
    c' B (x + y) = c' B x + c' B y
  smul : ∀ (B : Y.Opens) (r : Γ(Y, B)) (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B)),
    c B (r • x) = r * c B x
  smul' : ∀ (B : Y.Opens) (r : Γ(Y, B)) (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B)),
    c' B (r • x) = r * c' B x
  res : ∀ {B B' : Y.Opens} (h : B' ≤ B) (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B)),
    c B' (((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op x) =
      Y.presheaf.map (homOfLE h).op (c B x)
  res' : ∀ {B B' : Y.Opens} (h : B' ≤ B) (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B)),
    c' B' (((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op x) =
      Y.presheaf.map (homOfLE h).op (c' B x)
  gen : ∀ (V : X.Opens) (g : Γ(M, V)) (B : Y.Opens) (h : B ≤ f ⁻¹ᵁ V) (t : Y), t ∈ B →
    ∃ (B' : Y.Opens) (_ : t ∈ B') (h' : B' ≤ B),
      c B' (pullbackSectionsOn f M V B' (h'.trans h) g) = c' B' (pullbackSectionsOn f M V B' (h'.trans h) g)

namespace SectionMapPair

variable {f M}
variable {c c' : ∀ B : Y.Opens, Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B) → Γ(Y, B)}

theorem map_zero (H : SectionMapPair f M c c') (B : Y.Opens) : c B 0 = 0 := by
  have h := H.add B 0 0
  rw [add_zero] at h
  exact (add_left_cancel (a := c B 0) (by rw [add_zero]; exact h)).symm

theorem map_zero' (H : SectionMapPair f M c c') (B : Y.Opens) : c' B 0 = 0 := by
  have h := H.add' B 0 0
  rw [add_zero] at h
  exact (add_left_cancel (a := c' B 0) (by rw [add_zero]; exact h)).symm

attribute [local instance] AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra

/-- The inductive statement on the tensor product `O_{Y,t} ⊗ M_{f t}`: every element is the image of the germ of a
section `w` on a neighbourhood `B'` of `t` inside `B` on which `c` and `c'` agree. -/
theorem exists_germ_eq_tensorMap (H : SectionMapPair f M c c') (B : Y.Opens) (t : Y) (ht : t ∈ B)
    (z : AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensor f M t) :
    ∃ (B' : Y.Opens) (ht' : t ∈ B') (_ : B' ≤ B) (w : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B')),
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.germ B' t ht' w =
          AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap f M t z ∧ c B' w = c' B' w := by
  induction z using TensorProduct.induction_on with
  | zero =>
    refine ⟨B, ht, le_rfl, 0, ?_, ?_⟩
    · rw [_root_.map_zero, _root_.map_zero]
    · exact (H.map_zero B).trans (H.map_zero' B).symm
  | tmul r m =>
    obtain ⟨B₁, ht₁, ρ, rfl⟩ := Y.presheaf.exists_germ_eq r
    obtain ⟨V, hV, g, rfl⟩ := M.presheaf.exists_germ_eq m
    have ht₀ : t ∈ B ⊓ B₁ ⊓ f ⁻¹ᵁ V := ⟨⟨ht, ht₁⟩, hV⟩
    obtain ⟨B', ht', h', hgen⟩ := H.gen V g (B ⊓ B₁ ⊓ f ⁻¹ᵁ V) inf_le_right t ht₀
    have hB : B' ≤ B := h'.trans (inf_le_left.trans inf_le_left)
    have hB₁ : B' ≤ B₁ := h'.trans (inf_le_left.trans inf_le_right)
    refine ⟨B', ht', hB, Y.presheaf.map (homOfLE hB₁).op ρ • pullbackSectionsOn f M V B' (h'.trans inf_le_right) g,
      ?_, ?_⟩
    · rw [germ_smul_sections, AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap_tmul, TopCat.Presheaf.germ_res_apply]
      congr 1
      rw [pullbackSectionsOn_apply, TopCat.Presheaf.germ_res_apply]
      exact (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ f M t V hV g).symm
    · rw [H.smul, H.smul', hgen]
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨B₁, ht₁, hB₁, w₁, hw₁, hc₁⟩ := h₁
    obtain ⟨B₂, ht₂, hB₂, w₂, hw₂, hc₂⟩ := h₂
    have ht₁₂ : t ∈ B₁ ⊓ B₂ := ⟨ht₁, ht₂⟩
    refine ⟨B₁ ⊓ B₂, ht₁₂, inf_le_left.trans hB₁,
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE inf_le_left).op w₁ +
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE inf_le_right).op w₂, ?_, ?_⟩
    · rw [map_add, map_add, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hw₁, hw₂]
    · rw [H.add, H.add', H.res, H.res', H.res, H.res', hc₁, hc₂]

/-- **Comparison principle, local form**: `c B x` and `c' B x` agree on a neighbourhood of every point of `B`. -/
theorem exists_nhds_res_eq (H : SectionMapPair f M c c') (B : Y.Opens)
    (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B)) (t : Y) (ht : t ∈ B) :
    ∃ (B' : Y.Opens) (_ : t ∈ B') (h' : B' ≤ B),
      Y.presheaf.map (homOfLE h').op (c B x) = Y.presheaf.map (homOfLE h').op (c' B x) := by
  obtain ⟨z, hz⟩ := (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective f M t).2
    (((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.germ B t ht x)
  obtain ⟨B', ht', hB', w, hw, hc⟩ := H.exists_germ_eq_tensorMap B t ht z
  rw [hz] at hw
  obtain ⟨W, htW, iW', iW, hWeq⟩ :=
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.germ_eq t ht' ht w x hw
  refine ⟨W, htW, iW.le, ?_⟩
  have hWeq' : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE iW'.le).op w =
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE iW.le).op x := hWeq
  have e1 := H.res iW.le x
  have e2 := H.res' iW.le x
  have e3 := H.res iW'.le w
  have e4 := H.res' iW'.le w
  rw [← e1, ← e2, ← hWeq', e3, e4, hc]

/-- **Comparison principle**: the two families agree. -/
theorem eq (H : SectionMapPair f M c c') (B : Y.Opens)
    (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, B)) : c B x = c' B x := by
  choose B' htB' hB' heq using H.exists_nhds_res_eq B x
  let U : B → Y.Opens := fun t => B' t.1 t.2
  refine Y.sheaf.eq_of_locally_eq' U B (fun t => homOfLE (hB' t.1 t.2)) ?_ (c B x) (c' B x) fun t => heq t.1 t.2
  intro t ht
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨t, ht⟩, htB' t ht⟩

end SectionMapPair

end AlgebraicGeometry.Scheme.Modules

end
