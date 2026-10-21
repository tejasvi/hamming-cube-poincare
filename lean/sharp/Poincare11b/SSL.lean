/-
Corollary B2' + Lemma B3 (HSSL): for `θ ≥ 0`, `Im F_θ(q) = ∑_{k ≥ 1} β_k sin(2πkq)` on `[0,1]` with `β_k ≥ 0` summable.
`F_θ` is a finite sum `∑ e^{2πinq} ŝ(q)` with `n ∈ ℕ` and `s` symmetric unimodal; its coefficient sequence is
positively skewed.
-/
import Poincare11b.FourierFc

namespace Poincare11b

open Complex Real

/-- `F(q) = ∑_{(n,s) ∈ L} e^{2πinq} ŝ(q)` on `[0,1]`, with every `s` symmetric unimodal and `n ∈ ℕ`. -/
def Rep (F : ℝ → ℂ) : Prop :=
  ∃ L : List (ℕ × (ℤ → ℝ)), (∀ p ∈ L, SU p.2) ∧
    ∀ q ∈ Set.Icc (0 : ℝ) 1, F q = (L.map (fun p => ex p.1 q * fser p.2 q)).sum

lemma rep_one : Rep (fun _ => 1) :=
  ⟨[(0, delta0)], by simp [SU_delta0], fun q _ => by simp [ex_zero, fser_delta0]⟩

/-- `f_c = e^{2πimq} (ŝ₀ + e^{2πiq} ŝ₁)` on `[0,1]`, `s₀, s₁` symmetric unimodal (`c ≥ 0`). -/
lemma fc_decomp {c : ℝ} (hc : 0 ≤ c) : ∃ m : ℕ, ∃ s0 s1 : ℤ → ℝ, SU s0 ∧ SU s1 ∧
    ∀ q ∈ Set.Icc (0 : ℝ) 1, fc c q = ex m q * fser s0 q + ex ((m : ℤ) + 1) q * fser s1 q := by
  obtain ⟨m, s0, s1, h0, h1, hk⟩ := kap_decomp hc
  refine ⟨m, s0, s1, h0, h1, fun q hq => ?_⟩
  rw [fc_eq_fser c hq]
  have : kap c = shiftZ m s0 + shiftZ ((m : ℤ) + 1) s1 := by
    funext k; rw [hk k]; simp only [Pi.add_apply, shiftZ]; congr 2; ring
  rw [this, fser_add (NS_shift h0.1 _) (NS_shift h1.1 _), ← fser_shift, ← fser_shift]

lemma flat_sum (m : ℕ) (s0 s1 : ℤ → ℝ) (h0 : SU s0) (h1 : SU s1) (q : ℝ) :
    ∀ L : List (ℕ × (ℤ → ℝ)), (∀ p ∈ L, SU p.2) →
    (ex m q * fser s0 q + ex ((m : ℤ) + 1) q * fser s1 q) * (L.map (fun p => ex p.1 q * fser p.2 q)).sum =
    ((L.flatMap (fun p => [(m + p.1, conv s0 p.2), (m + 1 + p.1, conv s1 p.2)])).map
      (fun p => ex p.1 q * fser p.2 q)).sum
  | [], _ => by simp
  | p :: L, hL => by
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_nil, List.sum_nil, add_zero]
    rw [← flat_sum m s0 s1 h0 h1 q L (fun r hr => hL r (List.mem_cons_of_mem _ hr))]
    have hp := hL p List.mem_cons_self
    rw [← fser_mul h0.1 hp.1, ← fser_mul h1.1 hp.1]
    push_cast
    simp only [ex_add]
    ring

lemma rep_mul {F : ℝ → ℂ} (hF : Rep F) {c : ℝ} (hc : 0 ≤ c) : Rep (fun q => fc c q * F q) := by
  obtain ⟨L, hL, hFq⟩ := hF
  obtain ⟨m, s0, s1, h0, h1, hfc⟩ := fc_decomp hc
  refine ⟨L.flatMap (fun p => [(m + p.1, conv s0 p.2), (m + 1 + p.1, conv s1 p.2)]), ?_, fun q hq => ?_⟩
  · intro p hp
    rw [List.mem_flatMap] at hp
    obtain ⟨r, hr, hp⟩ := hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact SU_conv h0 (hL r hr)
    · exact SU_conv h1 (hL r hr)
  · show fc c q * F q = _
    rw [hfc q hq, hFq q hq]
    exact flat_sum m s0 s1 h0 h1 q L hL

/-- The coefficient sequence `P = ∑_{(n,s) ∈ L} shift_n s`. -/
def repSeq (L : List (ℕ × (ℤ → ℝ))) : ℤ → ℝ := (L.map (fun p => shiftZ p.1 p.2)).sum

lemma repSeq_props : ∀ L : List (ℕ × (ℤ → ℝ)), (∀ p ∈ L, SU p.2) →
    NS (repSeq L) ∧ (∀ q, (L.map (fun p => ex p.1 q * fser p.2 q)).sum = fser (repSeq L) q) ∧
      ∀ k : ℕ, repSeq L (-((k : ℤ) + 1)) ≤ repSeq L ((k : ℤ) + 1)
  | [], _ => by
    refine ⟨?_, fun q => ?_, fun k => ?_⟩
    · simpa [repSeq] using NS_zero
    · simp [repSeq, fser_zero]
    · simp [repSeq]
  | p :: L, hL => by
    obtain ⟨hNS, hF, hsk⟩ := repSeq_props L (fun r hr => hL r (List.mem_cons_of_mem _ hr))
    have hp := hL p List.mem_cons_self
    have hrep : repSeq (p :: L) = shiftZ p.1 p.2 + repSeq L := by
      simp [repSeq, List.map_cons, List.sum_cons]
    refine ⟨?_, fun q => ?_, fun k => ?_⟩
    · rw [hrep]; exact NS_add (NS_shift hp.1 _) hNS
    · rw [hrep, fser_add (NS_shift hp.1 _) hNS, ← hF q, ← fser_shift]
      simp [List.map_cons, List.sum_cons]
    · rw [hrep]
      simp only [Pi.add_apply, shiftZ]
      have := hp.skew p.1 k
      linarith [hsk k]

lemma rep_sine {F : ℝ → ℂ} (hF : Rep F) : ∃ β : ℕ → ℝ, (∀ k, 0 ≤ β k) ∧ Summable β ∧
    ∀ q ∈ Set.Icc (0 : ℝ) 1,
      HasSum (fun k : ℕ => β k * Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q)) (F q).im := by
  obtain ⟨L, hL, hFq⟩ := hF
  obtain ⟨hNS, hF, hsk⟩ := repSeq_props L hL
  refine ⟨fun k => repSeq L ((k : ℤ) + 1) - repSeq L (-((k : ℤ) + 1)), fun k => sub_nonneg.mpr (hsk k),
    ?_, fun q hq => ?_⟩
  · have hs : Summable (fun k : ℕ => repSeq L ((k : ℤ) + 1)) := by
      have hinj : Function.Injective (fun k : ℕ => (k : ℤ) + 1) := by
        intro a b h; simp only [add_left_inj, Nat.cast_inj] at h; exact h
      exact hNS.2.comp_injective hinj
    refine Summable.of_nonneg_of_le (fun k => sub_nonneg.mpr (hsk k)) (fun k => ?_) hs
    linarith [hNS.1 (-((k : ℤ) + 1))]
  · rw [hFq q hq, hF q]
    exact im_fser_hasSum hNS q

theorem rep_Fth : ∀ (n : ℕ) (θ : Fin n → ℝ), (∀ j, 0 ≤ θ j) → Rep (Fth θ)
  | 0, θ, _ => by
    have : Fth θ = fun _ => 1 := by funext q; simp [Fth]
    rw [this]; exact rep_one
  | n + 1, θ, hθ => by
    have : Fth θ = fun q => fc (θ 0) q * Fth (fun j => θ j.succ) q := by
      funext q; simp [Fth, Fin.prod_univ_succ]
    rw [this]
    exact rep_mul (rep_Fth n _ (fun j => hθ _)) (hθ 0)

/-- HSSL (Corollary B2' + Lemma B3). -/
theorem hSSL : HSSL := by
  intro n θ hθ
  obtain ⟨β, hβ0, hβs, hβ⟩ := rep_sine (rep_Fth n θ hθ)
  exact ⟨β, hβ0, hβs, fun q hq => (hβ q hq).tsum_eq.symm⟩

/-- The sine-series form with `HasSum` (used by HB and HPFA). -/
theorem sine_series {n : ℕ} (θ : Fin n → ℝ) (hθ : ∀ j, 0 ≤ θ j) : ∃ β : ℕ → ℝ, (∀ k, 0 ≤ β k) ∧ Summable β ∧
    ∀ q ∈ Set.Icc (0 : ℝ) 1,
      HasSum (fun k : ℕ => β k * Real.sin (2 * Real.pi * ((k : ℝ) + 1) * q)) (Fth θ q).im :=
  rep_sine (rep_Fth n θ hθ)

end Poincare11b
