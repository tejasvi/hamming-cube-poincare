/-
Symmetric unimodal (SU) sequences on ℤ: the convolution of two SU sequences is SU (pairing argument), and a
nonnegative shift of an SU sequence is positively skewed.
-/
import Poincare11b.ZSeries

namespace Poincare11b

/-- Symmetric unimodal: nonnegative, summable, even, nonincreasing on ℕ. -/
def SU (s : ℤ → ℝ) : Prop := NS s ∧ (∀ k, s (-k) = s k) ∧ ∀ k : ℕ, s ((k : ℤ) + 1) ≤ s k

lemma SU.eq_natAbs {s : ℤ → ℝ} (hs : SU s) (i : ℤ) : s i = s (i.natAbs : ℤ) := by
  rcases Int.natAbs_eq i with h | h
  · conv_lhs => rw [h]
  · conv_lhs => rw [h, hs.2.1]

/-- `s j ≤ s i` whenever `|i| ≤ |j|`. -/
lemma SU.le_of_natAbs_le {s : ℤ → ℝ} (hs : SU s) {i j : ℤ} (h : i.natAbs ≤ j.natAbs) : s j ≤ s i := by
  have hanti : Antitone (fun k : ℕ => s (k : ℤ)) :=
    antitone_nat_of_succ_le (fun k => by exact_mod_cast hs.2.2 k)
  rw [hs.eq_natAbs i, hs.eq_natAbs j]
  exact hanti h

lemma SU_delta0 : SU delta0 := by
  refine ⟨⟨fun k => by unfold delta0; split_ifs <;> norm_num, ?_⟩, fun k => ?_, fun k => ?_⟩
  · exact summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp at hk; simp [delta0, hk])
  · simp [delta0]
  · unfold delta0; split_ifs <;> first | (exfalso; omega) | norm_num

lemma SU_zero : SU 0 := ⟨NS_zero, fun _ => rfl, fun _ => le_rfl⟩

lemma SU_conv {s u : ℤ → ℝ} (hs : SU s) (hu : SU u) : SU (conv s u) := by
  refine ⟨NS_conv hs.1 hu.1, fun k => ?_, fun k => ?_⟩
  · -- evenness
    unfold conv
    rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1; funext j
    simp only [Equiv.neg_apply]
    rw [hs.2.1 j, show -k - -j = -(k - j) by ring, hu.2.1]
  · -- monotonicity: pair t with -1 - t
    have hP := summable_prod_conv hs.1 hu.1
    set K : ℤ := (k : ℤ) with hK
    let A : ℤ → ℝ := fun t => s (K - t) * u t
    let B : ℤ → ℝ := fun t => s (K - t) * u (t + 1)
    have hA : Summable A := by
      have := (Equiv.subLeft K).summable_iff.mpr (hP.prod_factor K)
      refine this.congr (fun t => ?_)
      simp only [Function.comp_apply, Equiv.subLeft_apply, A, sub_sub_cancel]
    have hB : Summable B := by
      have := (Equiv.subLeft K).summable_iff.mpr (hP.prod_factor (K + 1))
      refine this.congr (fun t => ?_)
      simp only [Function.comp_apply, Equiv.subLeft_apply, B]
      congr 2; ring
    have e1 : conv s u K = ∑' t, A t := by
      unfold conv
      rw [← (Equiv.subLeft K).tsum_eq]
      congr 1; funext t
      simp only [Equiv.subLeft_apply, A, sub_sub_cancel]
    have e2 : conv s u (K + 1) = ∑' t, B t := by
      unfold conv
      rw [← (Equiv.subLeft K).tsum_eq]
      congr 1; funext t
      simp only [Equiv.subLeft_apply, B]
      congr 2; ring
    let g : ℤ → ℝ := fun t => A t - B t
    have hg : Summable g := hA.sub hB
    have hg' : Summable (fun t => g (-1 - t)) := by
      have := (Equiv.subLeft (-1 : ℤ)).summable_iff.mpr hg
      exact this.congr (fun t => by simp only [Function.comp_apply, Equiv.subLeft_apply])
    have e3 : ∑' t, g t = ∑' t, g (-1 - t) := by
      rw [← (Equiv.subLeft (-1 : ℤ)).tsum_eq g]
      simp only [Equiv.subLeft_apply]
    have pair : ∀ t, 0 ≤ g t + g (-1 - t) := by
      intro t
      have hrw : g t + g (-1 - t) = (s (K - t) - s (K + 1 + t)) * (u t - u (t + 1)) := by
        simp only [g, A, B]
        rw [show K - (-1 - t) = K + 1 + t by ring, show -1 - t + 1 = -t by ring, hu.2.1 t,
          show -1 - t = -(t + 1) by ring, hu.2.1 (t + 1)]
        ring
      rw [hrw]
      rcases le_or_gt 0 t with ht | ht
      · apply mul_nonneg
        · exact sub_nonneg.mpr (hs.le_of_natAbs_le (by omega))
        · exact sub_nonneg.mpr (hu.le_of_natAbs_le (by omega))
      · apply mul_nonneg_of_nonpos_of_nonpos
        · exact sub_nonpos.mpr (hs.le_of_natAbs_le (by omega))
        · exact sub_nonpos.mpr (hu.le_of_natAbs_le (by omega))
    have e4 : 0 ≤ ∑' t, (g t + g (-1 - t)) := tsum_nonneg pair
    rw [hg.tsum_add hg', ← e3] at e4
    have e5 : ∑' t, g t = ∑' t, A t - ∑' t, B t := hA.tsum_sub hB
    have : conv s u (K + 1) ≤ conv s u K := by rw [e1, e2]; linarith
    exact_mod_cast this

/-- A nonnegative shift of an SU sequence is positively skewed. -/
lemma SU.skew {s : ℤ → ℝ} (hs : SU s) (n k : ℕ) :
    s (-((k : ℤ) + 1) - n) ≤ s ((k : ℤ) + 1 - n) :=
  hs.le_of_natAbs_le (by omega)

end Poincare11b
