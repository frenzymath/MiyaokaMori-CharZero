import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowMapIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.IsAmpleOfIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_AmpleTensorGloballyGenerated
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0892_Pointwise
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_QuasiAffineUnitAmple
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0892_QuasiSeparated
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01pw
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks01q3

/-! # Ampleness of `L ⊗ f^*M^{⊗a}` and of pullbacks along quasi-affine morphisms (Stacks 0892)

Stacks 0892: (1) if `L` is `f`-ample (`f` quasi-compact) and `M` is ample, then `L ⊗ f^*M^{⊗a}` is
ample for `a ≫ 0`; (2) if `M` is ample and `f` is quasi-affine (preimages of affine opens are
quasi-affine, e.g. finite or affine morphisms), then `f^*M` is ample.

Reference: Stacks 0892 (`morphisms-lemma-pullback-ample-tensor-relatively-ample`).

The two theorems are assembled from the modules `Stacks0892_*`:
* `Stacks0892_QuasiSeparated`: relatively ample ⇒ `f` quasi-separated; quasi-affine preimages of
  affine opens ⇒ `f` quasi-compact and quasi-separated. Together with
  `QuasiCompact.compactSpace_of_compactSpace`, `quasiSeparatedSpace_of_quasiSeparated` and
  `IsAmple.quasiSeparatedSpace` (01PY) this makes `X` quasi-compact and quasi-separated (first
  paragraph of the proof; only quasi-separatedness is needed, not the "separated" of the original).
* `Stacks0892_Pointwise`: the second paragraph pointwise — every `x` has `a, n ≥ 1` and
  `σ ∈ Γ((L ⊗ f^*M^{⊗a})^{⊗n})` with `x ∈ X_σ` affine (leaves: `Stacks0892_RestrictAmpleLocalSection`,
  `Stacks0892_ExtendLocalSection`, i.e. 01PW(2)).
* `Stacks0892_AmpleTensorGloballyGenerated` (Stacks 0890, pointwise) and Stacks 01Q3 (`M^{⊗c}` is
  globally generated for `c ≫ 0`): the third paragraph ("remove sufficiently divisible"). The proof
  here does not go through "sufficiently divisible": `X` is quasi-compact, so finitely many `X_{σ_i}`
  cover `X`; put `a₀ := max a_i + c₀`; for `a ≥ a₀` and `y ∈ X_{σ_i}` take `τ ∈ Γ(M^{⊗(a − a_i)})`
  nonvanishing at `f(y)` (01Q3); then `σ_i ⊗ (f^*τ)^{⊗n_i}` is a section of `(L ⊗ f^*M^{⊗a})^{⊗n_i}`
 (`stacks0892AddIso`) whose nonvanishing locus `X_{σ_i} ⊓ X_{f^*τ}` is affine (Stacks 01PV) and
  contains `y`.
* (2): quasi-affine preimages of affine opens ⇒ `O_X` is relatively ample for `f` (Stacks 0891 / 01P9,
  `IsAmple.unit_of_isQuasiAffine` + `IsAmple.of_iso (pullbackUnitIso …)`); then the pointwise lemma
  with `L = O_X` and `O_X ⊗ f^*M^{⊗a} ≅ (f^*M)^{⊗a}`, `((f^*M)^{⊗a})^{⊗n} ≅ (f^*M)^{⊗an}` (`an ≥ 1`)
  give the definition of `IsAmple (f^*M)` directly (01PT is not needed).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance isLineBundle_tensor_pullback_tensorPow {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (L : X.Modules) [L.IsLineBundle] (M : Y.Modules) [M.IsLineBundle]
    (a : ℕ) :
    (L.tensor ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (M.tensorPow a))).IsLineBundle := by
  letI hpow : (M.tensorPow a).IsLineBundle := SheafOfModules.IsLineBundle.tensorPow M a
  letI hpull : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (M.tensorPow a)).IsLineBundle :=
    SheafOfModules.IsLineBundle.pullback f (M.tensorPow a)
  exact SheafOfModules.IsLineBundle.tensor L _

/- Stacks 0892(1): `f` quasi-compact, `L` relatively ample for `f` (ample on the preimage of every
   affine open `V`, Stacks 01VJ(3)), `M` ample ⇒ there is `a₀` such that `L ⊗ f^*M^{⊗a}` is ample
   for all `a ≥ a₀`. -/

theorem AlgebraicGeometry.exists_isAmple_tensor_pullback_tensorPow {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f]
    (L : X.Modules) [L.IsLineBundle] (M : Y.Modules) [M.IsLineBundle]
    (hL : ∀ V : Y.affineOpens,
      AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj L))
    (hM : AlgebraicGeometry.IsAmple M) :
    ∃ a₀ : ℕ, ∀ a ≥ a₀, AlgebraicGeometry.IsAmple (AlgebraicGeometry.Scheme.Modules.tensor L
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M a))) := by
  -- first paragraph: X is quasi-compact and quasi-separated
  have hY : CompactSpace Y := hM.1
  have hX : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  have hYqs : QuasiSeparatedSpace Y := AlgebraicGeometry.IsAmple.quasiSeparatedSpace M hM
  have hfqs : AlgebraicGeometry.QuasiSeparated f :=
    AlgebraicGeometry.quasiSeparated_of_forall_isAmple_pullback f L hL
  have hXqs : QuasiSeparatedSpace X := AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated f
  -- second paragraph (pointwise): every point x has a x, n x, σ x
  choose a n ha hn σ hxσ haff using
    fun x : X => AlgebraicGeometry.exists_isAffineOpen_nonvanishingLocus_tensor_pullback_tensorPow f L M hL hM x
  -- X quasi-compact: finitely many X_{σ x} cover
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => ((AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor L
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M (a x)))) (n x)).nonvanishingLocus (σ x) : Set X))
    (fun x => (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor L
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M (a x)))) (n x)).nonvanishingLocus (σ x) |>.isOpen)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hxσ y⟩)
  -- third paragraph: M^{⊗c} is globally generated for c ≥ c₀ (Stacks 01Q3)
  obtain ⟨c₀, hc₀⟩ := AlgebraicGeometry.IsAmple.eventually_globallyGenerated M hM
  refine ⟨S.sup a + c₀, fun a' ha' => ⟨hX, fun y => ?_⟩⟩
  obtain ⟨i, hiS, hyi⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ y))
  have hai : a i + c₀ ≤ a' := le_trans (Nat.add_le_add_right (Finset.le_sup hiS) c₀) ha'
  obtain ⟨c, hc⟩ : ∃ c, a i + c = a' := ⟨a' - a i, by omega⟩
  have hcc₀ : c₀ ≤ c := by omega
  -- τ₀ ∈ Γ(Y, M^{⊗c}) does not vanish at f y; τ := f^*τ₀ does not vanish at y
  obtain ⟨τ₀, hτ₀⟩ := hc₀ c hcc₀ (f.base y)
  have hτ : ¬ IsZeroAt (sectionPullbackAlong f τ₀) y :=
    not_isZeroAt_sectionPullbackAlong f (AlgebraicGeometry.Scheme.Modules.tensorPow M c) τ₀ y hτ₀
  let τ : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M c), ⊤) :=
    sectionPullbackAlong f τ₀
  -- ρ ∈ Γ(((L ⊗ f^*M^{⊗ a i}) ⊗ f^*M^{⊗c})^{⊗ n i}), X_ρ = X_{σ i} ⊓ X_τ
  obtain ⟨ρ, hρ⟩ := AlgebraicGeometry.Scheme.Modules.exists_section_nonvanishingLocus_tensor_eq_inf
    (AlgebraicGeometry.Scheme.Modules.tensor L
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M (a i))))
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M c))
    (hn i) (σ i) τ
  let Φ := AlgebraicGeometry.Scheme.Modules.tensorPowMapIso
    (AlgebraicGeometry.Scheme.Modules.stacks0892AddIso f L M (a i) c a' hc) (n i)
  refine ⟨n i, hn i, Φ.hom.app ⊤ ρ, ?_, ?_⟩
  · rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso Φ ρ, hρ]
    refine ⟨hyi, ?_⟩
    show y ∈ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M c)).nonvanishingLocus τ
    exact hτ
  · rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso Φ ρ, hρ]
    exact (haff i).inf_nonvanishingLocus _ τ

/- Stacks 0892(2): `f` quasi-affine (the preimage of every affine open is a quasi-affine scheme,
   Stacks 01SK), `M` ample ⇒ `f^*M` ample. -/

theorem AlgebraicGeometry.IsAmple.pullback_of_isQuasiAffine {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (hf : ∀ V : Y.affineOpens, AlgebraicGeometry.Scheme.IsQuasiAffine (f ⁻¹ᵁ V.1))
    (M : Y.Modules) [M.IsLineBundle] (hM : AlgebraicGeometry.IsAmple M) :
    AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) := by
  -- the structure sheaf O_X is bound with `let`: instance search cannot see through the unfolding of
  -- `Scheme.Modules` to match `SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf`
  -- (the pullback/tensor instances fail on the bare unit)
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hY : CompactSpace Y := hM.1
  have hfqc : AlgebraicGeometry.QuasiCompact f := AlgebraicGeometry.quasiCompact_of_forall_isQuasiAffine f hf
  have hX : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  have hYqs : QuasiSeparatedSpace Y := AlgebraicGeometry.IsAmple.quasiSeparatedSpace M hM
  have hfqs : AlgebraicGeometry.QuasiSeparated f := AlgebraicGeometry.quasiSeparated_of_forall_isQuasiAffine f hf
  have hXqs : QuasiSeparatedSpace X := AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated f
  -- O_X is relatively ample for f (Stacks 0891 / 01P9)
  have hL : ∀ V : Y.affineOpens, AlgebraicGeometry.IsAmple
      ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj O) := by
    intro V
    have := hf V
    exact AlgebraicGeometry.IsAmple.of_iso (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (f ⁻¹ᵁ V.1).ι).symm
      (AlgebraicGeometry.IsAmple.unit_of_isQuasiAffine _)
  refine ⟨hX, fun x => ?_⟩
  obtain ⟨a, n, ha, hn, σ, hxσ, haff⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_nonvanishingLocus_tensor_pullback_tensorPow f O M hL hM x
  -- (O_X ⊗ f^*M^{⊗a})^{⊗n} ≅ (f^*M)^{⊗ an}
  let Ψ : AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor O
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M a))) n ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) (a * n) :=
    AlgebraicGeometry.Scheme.Modules.tensorPowMapIso
      (AlgebraicGeometry.Scheme.Modules.unitTensorLeftIso _ ≪≫
        AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso f M a) n ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorPowMulIso ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) a n
  refine ⟨a * n, Nat.mul_pos ha hn, Ψ.hom.app ⊤ σ, ?_, ?_⟩
  · rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso Ψ σ]
    exact hxσ
  · rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso Ψ σ]
    exact haff

end
