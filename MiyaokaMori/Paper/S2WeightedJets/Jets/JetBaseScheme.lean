import MiyaokaMori.Prelude

/-! # The jet base scheme

The jet parameter scheme `Spec k[t]/(t^{k+1})`, as a `k`-scheme (§2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The jet base `D_r = Spec k[t]/(t^{r+1})`; the ring is `GlobalTruncatedParameter k r`
(`= Jet.TruncatedJetRing k r = k[X] ⧸ (X^{r+1})`, the single spelling of this ring in the library). -/

noncomputable def jetBase (k : Type u) [Field k] (r : ℕ) : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))

noncomputable instance (k : Type u) [Field k] (r : ℕ) :
    (jetBase k r).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  AlgebraicGeometry.specOverSpec

end
