import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverCoherentQuotientTwists
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorLineBundleExact
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLes
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5tNoetherianProjectiveSpaceAux
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02uxAux
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.Stacks02uzExactAux
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic

/-! # Serre vanishing on projective space over a Noetherian ring

**Serre vanishing on `P^N_R`, `R` Noetherian** (Stacks 01YS(2) / 0B5T(4) for `X = P^N_R`): for a coherent
module `G` on `P^N_R = ProjectiveSpaceOver N R` and `p > 0` there is `n₀` with `H^p(P^N_R, G ⊗ O(n)) = 0`
for all `n ≥ n₀`. This is `Stacks0b5tProjectiveSpace.lean` with the field `k` replaced by a Noetherian ring
`R`; the proof is the same, step by step.

Proof (descending induction on `p`, Stacks 01YS). We prove: for every `m`, every `p > 0` with
`N + 1 ≤ p + m`, and every coherent `G`, the statement holds.
* `m = 0`, i.e. `p ≥ N + 1`: `H^p(P^N_R, −) = 0` on quasi-coherent modules by the Čech bound
  (`sheafCohomology_projectiveSpaceOver_subsingleton_of_lt`); `n₀ = 0`.
* `m + 1`: if `p > N` use the Čech bound again. Otherwise `N + 1 ≤ (p + 1) + m`. Choose an epimorphism
  `φ : ⨁_{j < r} O(d_j) ↠ G` (Stacks 01YS(1), `exists_epi_biproduct_twists_projectiveSpaceOver`: `O(1)` is
  ample on `P^N_R`, so Stacks 01Q3
  gives `⨁ O(1)^{⊗ -n} ↠ G`, and `O(1)^{⊗ -n} ≅ O(-n)`) and let
  `K := ker φ`. `K` is quasi-coherent (Stacks 01IC, `isQuasicoherent_kernel`) and hence coherent as a
  quasi-coherent submodule of the coherent module `⨁ O(d_j)` on the Noetherian scheme `P^N_R`
  (Stacks 01Y1, `isCoherent_of_mono`; `⨁ O(d_j)` is coherent since it is locally free of finite type,
  Stacks 01XZ). By induction, `H^{p+1}(K ⊗ O(n)) = 0` for `n ≥ n₁`; by the explicit computation on
  twisting sheaves over `R` (Stacks 01XT, `subsingleton_H_projectiveSpaceOverTwist_of_pos`),
  `H^p((⨁ O(d_j)) ⊗ O(n)) = ⨁ H^p(O(d_j + n)) = 0` for `n ≥ max_j (−N − d_j)⁺`
  (`subsingleton_H_biproduct_twists_tensor_twist_over`). Tensoring the short exact sequence
  `0 → K → ⨁ O(d_j) → G → 0` with the line bundle `O(n)` keeps it exact (tensoring with a line bundle is exact),
  and it stays exact in abelian sheaves (`bridge_shortExact_toSheaf`). For `n ≥ max n₁ n₂` the long exact
  sequence `H^p((⨁ O(d_j))(n)) → H^p(G(n)) → H^{p+1}(K(n))` (`subsingleton_H_X₃_of_shortExact`) gives
  `H^p(G(n)) = 0`.

Source: Stacks 01YS (proof of (2)), 0B5T (proof of (4)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- `H^p` of a finite biproduct of `O_X`-modules vanishes if each `H^p (g i)` does. Proof: `H^p` applied to
`𝟙 = ∑ π_j ≫ ι_j` (`biproduct.total`) shows `z = ∑_j H^p(ι_j)(H^p(π_j) z)`, and each `H^p(π_j) z` lies in the
zero group `H^p(g j)`. (Same statement as `subsingleton_H_biproduct` in `Stacks0b5tBiproductTwists.lean`,
which is not imported here.) -/
private theorem subsingleton_H_biproduct_over {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type} [Fintype ι] (g : ι → X.Modules) (p : ℕ)
    [∀ i, Subsingleton (CategoryTheory.Sheaf.H (g i).toAddCommGrpSheaf p)] :
    Subsingleton (CategoryTheory.Sheaf.H (⨁ g).toAddCommGrpSheaf p) := by
  classical
  let T : X.Modules ⥤ _ := SheafOfModules.toSheaf X.ringCatSheaf
  haveI : T.Additive := inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive
  -- `H^p(∑ f_j) z = ∑ H^p(f_j) z`
  have hsum : ∀ (s : Finset ι) (f : ι → ((⨁ g) ⟶ (⨁ g))) (z : CategoryTheory.Sheaf.H (⨁ g).toAddCommGrpSheaf p),
      Sheaf.H.map (T.map (∑ j ∈ s, f j)) p z = ∑ j ∈ s, Sheaf.H.map (T.map (f j)) p z := by
    intro s f z
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, T.map_zero]
      have h := Sheaf.H.map_add_apply (0 : T.obj (⨁ g) ⟶ T.obj (⨁ g)) 0 z
      rw [add_zero] at h
      exact (add_left_cancel ((add_zero _).trans h)).symm
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, T.map_add, Sheaf.H.map_add_apply, ih]
  have key : ∀ z : CategoryTheory.Sheaf.H (⨁ g).toAddCommGrpSheaf p, z = 0 := by
    intro z
    have htot : (∑ j, biproduct.π g j ≫ biproduct.ι g j) = 𝟙 (⨁ g) := biproduct.total
    have h1 : z = Sheaf.H.map (T.map (∑ j, biproduct.π g j ≫ biproduct.ι g j)) p z := by
      rw [htot, T.map_id]
      exact (Sheaf.H.map_id_apply z).symm
    rw [hsum] at h1
    refine h1.trans (Finset.sum_eq_zero fun j _ => ?_)
    rw [T.map_comp, Sheaf.H.map_comp_apply,
      Subsingleton.elim (Sheaf.H.map (T.map (biproduct.π g j)) p z) 0]
    exact map_zero _
  exact ⟨fun x y => (key x).trans (key y).symm⟩

/-- `(⨁_j O(d_j)) ⊗ O(n) ≅ ⨁_j O(d_j + n)` on `P^N_R`. -/
theorem biproduct_projectiveSpaceOverTwist_tensor_twist_iso (R : Type u) [CommRing R] (N : ℕ) {r : ℕ}
    (d : Fin r → ℤ) (n : ℤ) :
    Nonempty ((CategoryTheory.Limits.biproduct (fun j => projectiveSpaceOverTwist R N (d j))).tensor
        (projectiveSpaceOverTwist R N n) ≅
      CategoryTheory.Limits.biproduct (fun j => projectiveSpaceOverTwist R N (d j + n))) := by
  let B := projectiveSpaceOverTwist R N n
  let f : Fin r → (ProjectiveSpaceOver N R).Modules := fun j => projectiveSpaceOverTwist R N (d j)
  haveI : (CategoryTheory.MonoidalCategory.tensorRight B).IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle B
  have e₁ : (⨁ f) ⊗ B ≅ ⨁ fun j => f j ⊗ B :=
    (CategoryTheory.MonoidalCategory.tensorRight B).mapIso (biproduct.isoCoproduct f) ≪≫
      PreservesCoproduct.iso (CategoryTheory.MonoidalCategory.tensorRight B) f ≪≫
      (biproduct.isoCoproduct (fun j => f j ⊗ B)).symm
  have e₂ : ∀ j, f j ⊗ B ≅ projectiveSpaceOverTwist R N (d j + n) := fun j =>
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (f j) B).symm ≪≫
      (projectiveSpaceOverTwist_tensor R N (d j) n).some
  exact ⟨AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (⨁ f) B ≪≫ e₁ ≪≫
    biproduct.mapIso e₂⟩

/-- **Vanishing of the free part over a ring** (Stacks 01XT + 01YS): for `d : Fin r → ℤ` and `p > 0`,
`H^p(P^N_R, (⨁_j O(d_j)) ⊗ O(n)) = 0` for all `n ≥ max_j (−N − d_j)⁺`. -/
theorem AlgebraicGeometry.subsingleton_H_biproduct_twists_tensor_twist_over (R : Type u) [CommRing R]
    (N : ℕ) {r : ℕ} (d : Fin r → ℤ) (p : ℕ) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Subsingleton (CategoryTheory.Sheaf.H
      ((CategoryTheory.Limits.biproduct (fun j => projectiveSpaceOverTwist R N (d j))).tensor
        (projectiveSpaceOverTwist R N n)).toAddCommGrpSheaf p) := by
  refine ⟨Finset.univ.sup (fun j => Int.toNat (-(N : ℤ) - d j)), fun n hn => ?_⟩
  obtain ⟨e⟩ := biproduct_projectiveSpaceOverTwist_tensor_twist_iso R N d n
  haveI hz : ∀ j, Subsingleton (CategoryTheory.Sheaf.H
      (projectiveSpaceOverTwist R N (d j + n)).toAddCommGrpSheaf p) := by
    intro j
    have h₁ : Int.toNat (-(N : ℤ) - d j) ≤ n :=
      (Finset.le_sup (f := fun j => Int.toNat (-(N : ℤ) - d j)) (Finset.mem_univ j)).trans hn
    have h₂ : -(N : ℤ) - d j ≤ n := Int.toNat_le.mp h₁
    exact subsingleton_H_projectiveSpaceOverTwist_of_pos R N (d j + n) p hp (by omega)
  haveI : Subsingleton (CategoryTheory.Sheaf.H
      (⨁ fun j => projectiveSpaceOverTwist R N (d j + n)).toAddCommGrpSheaf p) :=
    subsingleton_H_biproduct_over (fun j => projectiveSpaceOverTwist R N (d j + n)) p
  exact CategoryTheory.Sheaf.subsingleton_H_of_iso
    ((SheafOfModules.toSheaf.{u} (ProjectiveSpaceOver N R).ringCatSheaf).mapIso e).symm p

/-- A finite direct sum of twisting sheaves on `P^N_R`, `R` Noetherian, is coherent (locally free of
finite type on a locally Noetherian scheme, Stacks 01XZ). -/
theorem biproduct_projectiveSpaceOverTwist_isCoherent (R : Type u) [CommRing R] [IsNoetherianRing R]
    (N : ℕ) {r : ℕ} (d : Fin r → ℤ) :
    (⨁ fun j => projectiveSpaceOverTwist R N (d j)).IsCoherent := by
  haveI := ProjectiveSpaceOver.isLocallyNoetherian' R N
  exact AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree _

/-- **Serre vanishing on `P^N_R`, `R` Noetherian** (Stacks 01YS(2)): `H^p(P^N_R, G ⊗ O(n)) = 0` for `p > 0`,
`G` coherent and `n ≫ 0`. -/
theorem AlgebraicGeometry.sheafCohomology_tensor_twist_subsingleton_projectiveSpaceOver (R : Type u)
    [CommRing R] [IsNoetherianRing R] (N : ℕ) (G : (ProjectiveSpaceOver N R).Modules) [G.IsCoherent]
    (p : ℕ) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Subsingleton (CategoryTheory.Sheaf.H
      (G.tensor (projectiveSpaceOverTwist R N n)).toAddCommGrpSheaf p) := by
  haveI := ProjectiveSpaceOver.isLocallyNoetherian' R N
  -- Čech bound, used twice below
  have bound : ∀ (G : (ProjectiveSpaceOver N R).Modules) (_ : G.IsCoherent) (p : ℕ), N < p →
      ∀ n : ℕ, Subsingleton (CategoryTheory.Sheaf.H
        (G.tensor (projectiveSpaceOverTwist R N n)).toAddCommGrpSheaf p) := by
    intro G hG p hp n
    haveI : G.IsQuasicoherent := hG.quasicoherent
    exact AlgebraicGeometry.sheafCohomology_projectiveSpaceOver_subsingleton_of_lt N _ p hp
  suffices key : ∀ m : ℕ, ∀ p : ℕ, N + 1 ≤ p + m → 0 < p →
      ∀ (G : (ProjectiveSpaceOver N R).Modules), G.IsCoherent →
        ∃ n₀ : ℕ, ∀ n ≥ n₀, Subsingleton (CategoryTheory.Sheaf.H
          (G.tensor (projectiveSpaceOverTwist R N n)).toAddCommGrpSheaf p) from
    key (N + 1) p (by omega) hp G inferInstance
  intro m
  induction m with
  | zero =>
    intro p hp _ G hG
    exact ⟨0, fun n _ => bound G hG p (by omega) n⟩
  | succ m ih =>
    intro p hp hp0 G hG
    by_cases hN : N < p
    · exact ⟨0, fun n _ => bound G hG p hN n⟩
    -- the presentation `0 → K → ⨁ O(d_j) → G → 0`
    obtain ⟨r, d, φ, hφ⟩ := exists_epi_biproduct_twists_projectiveSpaceOver R N G
    haveI : (⨁ fun j => projectiveSpaceOverTwist R N (d j)).IsCoherent :=
      biproduct_projectiveSpaceOverTwist_isCoherent R N d
    haveI : (⨁ fun j => projectiveSpaceOverTwist R N (d j)).IsQuasicoherent :=
      AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
    haveI : G.IsQuasicoherent := hG.quasicoherent
    haveI hKqc : (kernel φ).IsQuasicoherent :=
      (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel φ).1
    have hKc : (kernel φ).IsCoherent :=
      AlgebraicGeometry.Scheme.Modules.isCoherent_of_mono (kernel.ι φ)
    obtain ⟨n₁, hn₁⟩ := ih (p + 1) (by omega) (by omega) (kernel φ) hKc
    obtain ⟨n₂, hn₂⟩ := AlgebraicGeometry.subsingleton_H_biproduct_twists_tensor_twist_over R N d p hp0
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    -- the short exact sequence and its twist by `O(n)`
    let S : ShortComplex (ProjectiveSpaceOver N R).Modules :=
      ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel φ)
        mono_f := inferInstanceAs (Mono (kernel.ι φ))
        epi_g := hφ }
    obtain ⟨T, e₁, e₂, e₃, -, -, hT⟩ :=
      AlgebraicGeometry.Scheme.Modules.shortExact_tensor_lineBundle (projectiveSpaceOverTwist R N n) S hS
    have hT' := bridge_shortExact_toSheaf
      (ShortComplex.mk (C := SheafOfModules.{u} (ProjectiveSpaceOver N R).ringCatSheaf) T.f T.g T.zero) hT
    -- the two outer terms vanish
    haveI h₂ : Subsingleton (CategoryTheory.Sheaf.H T.X₂.toAddCommGrpSheaf p) :=
      CategoryTheory.Sheaf.subsingleton_H_of_iso (hF := hn₂ n (le_of_max_le_right hn))
        ((SheafOfModules.toSheaf (ProjectiveSpaceOver N R).ringCatSheaf).mapIso
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫ e₂.symm)) p
    haveI h₁ : Subsingleton (CategoryTheory.Sheaf.H T.X₁.toAddCommGrpSheaf (p + 1)) :=
      CategoryTheory.Sheaf.subsingleton_H_of_iso (hF := hn₁ n (le_of_max_le_left hn))
        ((SheafOfModules.toSheaf (ProjectiveSpaceOver N R).ringCatSheaf).mapIso
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫ e₁.symm)) (p + 1)
    haveI h₂' : Subsingleton (CategoryTheory.Sheaf.H
        ((ShortComplex.mk (C := SheafOfModules.{u} (ProjectiveSpaceOver N R).ringCatSheaf) T.f T.g T.zero).map
          (SheafOfModules.toSheaf (ProjectiveSpaceOver N R).ringCatSheaf)).X₂ p) := h₂
    haveI h₁' : Subsingleton (CategoryTheory.Sheaf.H
        ((ShortComplex.mk (C := SheafOfModules.{u} (ProjectiveSpaceOver N R).ringCatSheaf) T.f T.g T.zero).map
          (SheafOfModules.toSheaf (ProjectiveSpaceOver N R).ringCatSheaf)).X₁ (p + 1)) := h₁
    haveI h₃ : Subsingleton (CategoryTheory.Sheaf.H T.X₃.toAddCommGrpSheaf p) :=
      CategoryTheory.Sheaf.subsingleton_H_X₃_of_shortExact hT' p (p + 1) rfl
    exact CategoryTheory.Sheaf.subsingleton_H_of_iso
      ((SheafOfModules.toSheaf (ProjectiveSpaceOver N R).ringCatSheaf).mapIso
        (e₃ ≪≫ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm)) p

end
