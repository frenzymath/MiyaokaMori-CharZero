import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionRing
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowMapIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0892_ExtendLocalSection
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0c4k_IsAmplePullbackIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0892_RestrictAmpleLocalSection
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowSectionLocus

/-! # The pointwise step of Stacks 0892

The pointwise form of the second paragraph of the proof of Stacks 0892: if `X` is quasi-compact and
quasi-separated, `L` is relatively ample for `f` (ample on preimages of affine opens), `M` is ample
and `x ∈ X`, then there are `a, n ≥ 1` and `σ ∈ Γ(X, (L ⊗ f^*M^{⊗a})^{⊗n})` with `x ∈ X_σ` and `X_σ`
affine.

Reference: Stacks 0892, second paragraph of the proof
(`morphisms-lemma-pullback-ample-tensor-relatively-ample`). Assembled from:
* `nonvanishingLocus_sectionPullbackAlong`: `f^{-1}(Y_t) = X_{f^*t}`;
* `Stacks0892_RestrictAmpleLocalSection`: `L|_{X_{f^*t}}` ample ⇒ a local section `s` and an affine
  open `W ∋ x`;
* `Stacks0892_ExtendLocalSection` (Stacks 01PW(2)): extension to `σ₀ ∈ Γ(L^{⊗n} ⊗ N^{⊗e})` with
  `X_{σ₀} ⊓ X_{f^*t} = W`;
* the nonvanishing locus of `σ₁ := σ₀ ⊗ (f^*t)^{⊗b}` (`b := (e+1)n − e ≥ 1`) is `X_{σ₀} ⊓ X_{f^*t} = W`;
* the rearrangement `L^{⊗n} ⊗ N^{⊗e} ⊗ N^{⊗b} ≅ (L ⊗ f^*M^{⊗ m(e+1)})^{⊗n}` (`e + b = (e+1)n`,
  `N = f^*M^{⊗m}`); nonvanishing loci are invariant under isomorphisms.

Proof steps (following the original paragraph): take `m ≥ 1` and `t ∈ Γ(Y, M^{⊗m})` with
`f(x) ∈ Y_t` affine (`M` ample); `U := X_{f^*t} = f^{-1}(Y_t)`; `L|_U` ample gives `n ≥ 1`,
`s ∈ Γ(U, L^{⊗n})` and an affine open `W ∋ x`; extend by 01PW(2); choose `b` with `n ∣ e + b`;
rearrange into an `n`-th power; `a := m(e+1)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The rearrangement isomorphism `(L^{⊗n} ⊗ N^{⊗e}) ⊗ N^{⊗b} ≅ (L ⊗ f^*M^{⊗ m(e+1)})^{⊗n}`, where
`N = f^*M^{⊗m}` and `e + b = (e+1)n`. -/
noncomputable def stacks0892RearrangeIso {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (L : X.Modules) (M : Y.Modules) (m n e b : ℕ) (h : e + b = (e + 1) * n) :
    AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L n)
          (AlgebraicGeometry.Scheme.Modules.tensorPow
            ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M m)) e))
        (AlgebraicGeometry.Scheme.Modules.tensorPow
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M m)) b) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow
        (AlgebraicGeometry.Scheme.Modules.tensor L
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow M (m * (e + 1))))) n :=
  let N : X.Modules := (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M m)
  -- N^{⊗e} ⊗ N^{⊗b} ≅ (N^{⊗(e+1)})^{⊗n}
  let φ : AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow N e)
      (AlgebraicGeometry.Scheme.Modules.tensorPow N b) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow N (e + 1)) n :=
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso N e b).symm ≪≫
      CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.tensorPow N) h) ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso N (e + 1) n).symm
  -- N^{⊗(e+1)} ≅ f^*(M^{⊗ m(e+1)})
  let ψ : AlgebraicGeometry.Scheme.Modules.tensorPow N (e + 1) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow M (m * (e + 1))) :=
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso f (AlgebraicGeometry.Scheme.Modules.tensorPow M m) (e + 1)).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).mapIso (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso M m (e + 1))
  AlgebraicGeometry.Scheme.Modules.tensorAssocIso _ _ _ ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso _ φ ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorPowTensorIso L (AlgebraicGeometry.Scheme.Modules.tensorPow N (e + 1)) n).symm ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorPowMapIso (AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso L ψ) n

/-- The addition isomorphism `(L ⊗ f^*M^{⊗a}) ⊗ f^*M^{⊗c} ≅ L ⊗ f^*M^{⊗a'}` (`a + c = a'`). -/
noncomputable def stacks0892AddIso {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (L : X.Modules) (M : Y.Modules) (a c a' : ℕ) (h : a + c = a') :
    AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensor L
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M a)))
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M c)) ≅
      AlgebraicGeometry.Scheme.Modules.tensor L
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M a')) :=
  AlgebraicGeometry.Scheme.Modules.tensorAssocIso _ _ _ ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso L
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso f _ _).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).mapIso
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
            (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso M a c).symm ≪≫
            CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.tensorPow M) h)))

end AlgebraicGeometry.Scheme.Modules

/-- **Second paragraph of the proof of Stacks 0892 (pointwise)**: `X` quasi-compact and
quasi-separated, `L` relatively ample for `f`, `M` ample; then every point `x` has `a, n ≥ 1` and
`σ ∈ Γ((L ⊗ f^*M^{⊗a})^{⊗n})` with `x ∈ X_σ` affine. -/
theorem AlgebraicGeometry.exists_isAffineOpen_nonvanishingLocus_tensor_pullback_tensorPow
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsLineBundle] (M : Y.Modules) [M.IsLineBundle]
    (hL : ∀ V : Y.affineOpens,
      AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj L))
    (hM : AlgebraicGeometry.IsAmple M) (x : X) :
    ∃ (a n : ℕ) (_ : 0 < a) (_ : 0 < n)
      (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor L
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M a))) n, ⊤)),
      x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor L
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M a))) n).nonvanishingLocus σ ∧
      AlgebraicGeometry.IsAffineOpen ((AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor L
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M a))) n).nonvanishingLocus σ) := by
  obtain ⟨m, hm, t, hft, haffV⟩ := hM.2 (f.base x)
  -- N := f^*(M^{⊗m}), τ := f^*t, U := X_τ = f⁻¹(Y_t)
  let N : X.Modules := (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensorPow M m)
  let τ : Γ(N, ⊤) := sectionPullbackAlong f (t : ((AlgebraicGeometry.Scheme.Modules.tensorPow M m).val.obj (Opposite.op ⊤) : Type u))
  have hU : N.nonvanishingLocus τ = f ⁻¹ᵁ (AlgebraicGeometry.Scheme.Modules.tensorPow M m).nonvanishingLocus t :=
    AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_sectionPullbackAlong f
      (AlgebraicGeometry.Scheme.Modules.tensorPow M m)
      (t : ((AlgebraicGeometry.Scheme.Modules.tensorPow M m).val.obj (Opposite.op ⊤) : Type u))
  have hLV : AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback
      (f ⁻¹ᵁ (AlgebraicGeometry.Scheme.Modules.tensorPow M m).nonvanishingLocus t).ι).obj L) :=
    hL ⟨_, haffV⟩
  have hLU : AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback
      (N.nonvanishingLocus τ).ι).obj L) :=
    (congrArg (fun U : X.Opens => AlgebraicGeometry.IsAmple
      ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj L)) hU).mpr hLV
  have hxU : x ∈ N.nonvanishingLocus τ := by
    rw [hU]
    exact hft
  obtain ⟨n, hn, s, W, hxW, hWU, haffW, hW⟩ :=
    AlgebraicGeometry.IsAmple.exists_local_section_of_restrict L (N.nonvanishingLocus τ) hLU x hxU
  obtain ⟨e, σ₀, hσ₀⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_section_nonvanishingLocus_inf_eq N τ
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n) s W hWU hW
  -- b := (e+1)n − e ≥ 1, e + b = (e+1)n
  have hle : e + 1 ≤ (e + 1) * n := Nat.le_mul_of_pos_right (e + 1) hn
  have hb : 0 < (e + 1) * n - e := by omega
  have hEB : e + ((e + 1) * n - e) = (e + 1) * n := by omega
  -- σ₁ := σ₀ ⊗ τ^{⊗b}, X_{σ₁} = X_{σ₀} ⊓ X_τ = W
  let σ₁ : Γ(AlgebraicGeometry.Scheme.Modules.tensor
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L n)
        (AlgebraicGeometry.Scheme.Modules.tensorPow N e))
      (AlgebraicGeometry.Scheme.Modules.tensorPow N ((e + 1) * n - e)), ⊤) :=
    sectionTensor σ₀ (AlgebraicGeometry.Scheme.Modules.tensorPowSection
      (τ : (N.val.obj (Opposite.op ⊤) : Type u)) ((e + 1) * n - e))
  have hσ₁ : (AlgebraicGeometry.Scheme.Modules.tensor
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L n)
        (AlgebraicGeometry.Scheme.Modules.tensorPow N e))
      (AlgebraicGeometry.Scheme.Modules.tensorPow N ((e + 1) * n - e))).nonvanishingLocus σ₁ = W := by
    have h2 := AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_sectionTensor
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L n)
        (AlgebraicGeometry.Scheme.Modules.tensorPow N e))
      (AlgebraicGeometry.Scheme.Modules.tensorPow N ((e + 1) * n - e)) σ₀
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection (τ : (N.val.obj (Opposite.op ⊤) : Type u)) ((e + 1) * n - e))
    have h3 := AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tensorPowSection N τ hb
    exact h2.trans ((congrArg (fun W' => (AlgebraicGeometry.Scheme.Modules.tensor
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n)
        (AlgebraicGeometry.Scheme.Modules.tensorPow N e)).nonvanishingLocus σ₀ ⊓ W') h3).trans hσ₀)
  let Φ := AlgebraicGeometry.Scheme.Modules.stacks0892RearrangeIso f L M m n e ((e + 1) * n - e) hEB
  refine ⟨m * (e + 1), n, Nat.mul_pos hm (Nat.succ_pos e), hn, Φ.hom.app ⊤ σ₁, ?_, ?_⟩
  · rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso Φ σ₁, hσ₁]
    exact hxW
  · rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso Φ σ₁, hσ₁]
    exact haffW

end
