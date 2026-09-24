import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceCoherentQuotientTwists
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorLineBundleExact
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLes
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5tBiproductTwists
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5tProjectiveSpaceAux
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02uxAux
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree

/-! # Serre vanishing on projective space

**Serre vanishing on projective space** (Stacks 01YS(2) / 0B5T(4) for `X = P^N_k`): for a coherent
module `G` on `P^N_k` and `p > 0` there is `n₀` with `H^p(P^N, G ⊗ O(n)) = 0` for all `n ≥ n₀`.

Proof (descending induction on `p`, Stacks 01YS). We prove: for every `m`, every `p > 0` with
`N + 1 ≤ p + m`, and every coherent `G`, the statement holds.
* `m = 0`, i.e. `p ≥ N + 1`: `H^p(P^N, −) = 0` on quasi-coherent modules by the Čech bound
  (`sheafCohomology_projectiveSpace_subsingleton_of_lt`, `Stacks0b5tProjectiveSpaceAux.lean`);
  `n₀ = 0`.
* `m + 1`: if `p > N` use the Čech bound again. Otherwise `N + 1 ≤ (p + 1) + m`. Choose an epimorphism
  `φ : ⨁_{j < r} O(d_j) ↠ G` (Stacks 01YS(1), `exists_epi_biproduct_twists_projectiveSpace`) and let
  `K := ker φ`. `K` is quasi-coherent
  (kernels of maps of quasi-coherent modules, Stacks 01IC, `isQuasicoherent_kernel`) and hence coherent as
  a quasi-coherent submodule of the coherent module `⨁ O(d_j)` on the Noetherian scheme `P^N_k`
  (Stacks 01Y1, `isCoherent_of_mono`; `⨁ O(d_j)` is coherent since it is locally free of finite type,
  Stacks 01XZ). By induction, `H^{p+1}(K ⊗ O(n)) = 0` for `n ≥ n₁`; by the explicit computation on
  twisting sheaves, `H^p((⨁ O(d_j)) ⊗ O(n)) = 0` for `n ≥ n₂` (`Stacks0b5tBiproductTwists.lean`).
  Tensoring the short exact sequence `0 → K → ⨁ O(d_j) → G → 0` with the line bundle `O(n)` keeps it
  exact (tensoring with a line bundle is exact), and it stays exact in abelian sheaves
  (`bridge_shortExact_toSheaf`). For `n ≥ max n₁ n₂` the long exact sequence
  `H^p((⨁ O(d_j))(n)) → H^p(G(n)) → H^{p+1}(K(n))` (`subsingleton_H_X₃_of_shortExact`) gives
  `H^p(G(n)) = 0`.

Source: Stacks 01YS (proof of (2)), 0B5T (proof of (4)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- `P^N_k` is locally Noetherian (finite type over the field `k`). -/
theorem ProjectiveSpace.isLocallyNoetherian (k : Type u) [Field k] (N : ℕ) :
    AlgebraicGeometry.IsLocallyNoetherian (ProjectiveSpace N k) :=
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
    (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-- A finite direct sum of twisting sheaves on `P^N_k` is coherent (locally free of finite type on a
locally Noetherian scheme, Stacks 01XZ). -/
theorem biproduct_projectiveSpaceTwist_isCoherent {k : Type u} [Field k] (N : ℕ) {r : ℕ}
    (d : Fin r → ℤ) :
    (⨁ fun j => projectiveSpaceTwist k N (d j)).IsCoherent := by
  haveI := ProjectiveSpace.isLocallyNoetherian k N
  exact AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree _

/-- **Serre vanishing on `P^N_k`** (Stacks 01YS(2)): `H^p(P^N, G ⊗ O(n)) = 0` for `p > 0`, `G` coherent
and `n ≫ 0`. -/
theorem AlgebraicGeometry.sheafCohomology_tensor_twist_subsingleton_projectiveSpace {k : Type u}
    [Field k] (N : ℕ) (G : (ProjectiveSpace N k).Modules) [G.IsCoherent] (p : ℕ) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Subsingleton (CategoryTheory.Sheaf.H
      (G.tensor (projectiveSpaceTwist k N n)).toAddCommGrpSheaf p) := by
  haveI := ProjectiveSpace.isLocallyNoetherian k N
  -- Čech bound, used twice below
  have bound : ∀ (G : (ProjectiveSpace N k).Modules) (_ : G.IsCoherent) (p : ℕ), N < p →
      ∀ n : ℕ, Subsingleton (CategoryTheory.Sheaf.H
        (G.tensor (projectiveSpaceTwist k N n)).toAddCommGrpSheaf p) := by
    intro G hG p hp n
    haveI : G.IsQuasicoherent := hG.quasicoherent
    exact AlgebraicGeometry.sheafCohomology_projectiveSpace_subsingleton_of_lt N _ p hp
  suffices key : ∀ m : ℕ, ∀ p : ℕ, N + 1 ≤ p + m → 0 < p →
      ∀ (G : (ProjectiveSpace N k).Modules), G.IsCoherent →
        ∃ n₀ : ℕ, ∀ n ≥ n₀, Subsingleton (CategoryTheory.Sheaf.H
          (G.tensor (projectiveSpaceTwist k N n)).toAddCommGrpSheaf p) from
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
    obtain ⟨r, d, φ, hφ⟩ := exists_epi_biproduct_twists_projectiveSpace N G
    haveI : (⨁ fun j => projectiveSpaceTwist k N (d j)).IsCoherent :=
      biproduct_projectiveSpaceTwist_isCoherent N d
    haveI : (⨁ fun j => projectiveSpaceTwist k N (d j)).IsQuasicoherent :=
      AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
    haveI : G.IsQuasicoherent := hG.quasicoherent
    haveI hKqc : (kernel φ).IsQuasicoherent :=
      (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel φ).1
    have hKc : (kernel φ).IsCoherent :=
      AlgebraicGeometry.Scheme.Modules.isCoherent_of_mono (kernel.ι φ)
    obtain ⟨n₁, hn₁⟩ := ih (p + 1) (by omega) (by omega) (kernel φ) hKc
    obtain ⟨n₂, hn₂⟩ := AlgebraicGeometry.subsingleton_H_biproduct_twists_tensor_twist (k := k) N d p hp0
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    -- the short exact sequence and its twist by `O(n)`
    let S : ShortComplex (ProjectiveSpace N k).Modules :=
      ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel φ)
        mono_f := inferInstanceAs (Mono (kernel.ι φ))
        epi_g := hφ }
    obtain ⟨T, e₁, e₂, e₃, -, -, hT⟩ :=
      AlgebraicGeometry.Scheme.Modules.shortExact_tensor_lineBundle (projectiveSpaceTwist k N n) S hS
    have hT' := bridge_shortExact_toSheaf
      (ShortComplex.mk (C := SheafOfModules.{u} (ProjectiveSpace N k).ringCatSheaf) T.f T.g T.zero) hT
    -- the two outer terms vanish
    haveI h₂ : Subsingleton (CategoryTheory.Sheaf.H T.X₂.toAddCommGrpSheaf p) :=
      CategoryTheory.Sheaf.subsingleton_H_of_iso (hF := hn₂ n (le_of_max_le_right hn))
        ((SheafOfModules.toSheaf (ProjectiveSpace N k).ringCatSheaf).mapIso
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫ e₂.symm)) p
    haveI h₁ : Subsingleton (CategoryTheory.Sheaf.H T.X₁.toAddCommGrpSheaf (p + 1)) :=
      CategoryTheory.Sheaf.subsingleton_H_of_iso (hF := hn₁ n (le_of_max_le_left hn))
        ((SheafOfModules.toSheaf (ProjectiveSpace N k).ringCatSheaf).mapIso
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫ e₁.symm)) (p + 1)
    haveI h₂' : Subsingleton (CategoryTheory.Sheaf.H
        ((ShortComplex.mk (C := SheafOfModules.{u} (ProjectiveSpace N k).ringCatSheaf) T.f T.g T.zero).map
          (SheafOfModules.toSheaf (ProjectiveSpace N k).ringCatSheaf)).X₂ p) := h₂
    haveI h₁' : Subsingleton (CategoryTheory.Sheaf.H
        ((ShortComplex.mk (C := SheafOfModules.{u} (ProjectiveSpace N k).ringCatSheaf) T.f T.g T.zero).map
          (SheafOfModules.toSheaf (ProjectiveSpace N k).ringCatSheaf)).X₁ (p + 1)) := h₁
    haveI h₃ : Subsingleton (CategoryTheory.Sheaf.H T.X₃.toAddCommGrpSheaf p) :=
      CategoryTheory.Sheaf.subsingleton_H_X₃_of_shortExact hT' p (p + 1) rfl
    exact CategoryTheory.Sheaf.subsingleton_H_of_iso
      ((SheafOfModules.toSheaf (ProjectiveSpace N k).ringCatSheaf).mapIso
        (e₃ ≪≫ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm)) p

end
