import Kusner5.Orders

/-!
Finite physical box geometry and the agreement-form cycle budget used by the
arbitrary ORIGINAL quartet argument. These are elementary real lemmas. The
original-to-box bridge belongs to `Quartet.lean`; no geometric hypothesis from
this module may be added to the public Kusner theorem.
-/

open scoped BigOperators

namespace Kusner5
namespace QuartetGeometry

def InSymmetricBox {ι : Type*} (lam v : ι → ℝ) : Prop :=
  ∀ i, -lam i ≤ v i ∧ v i ≤ lam i

private theorem box_sum_adjust_down {ι : Type*} [Fintype ι]
    (lam v : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hv : InSymmetricBox lam v)
    (T : ℝ) (hT : -(∑ i, lam i) ≤ T) (hTv : T ≤ ∑ i, v i) :
    ∃ z : ι → ℝ, InSymmetricBox lam z ∧
      (∀ i, z i ≤ v i) ∧ (∑ i, z i) = T ∧
      (∑ i, |z i - v i|) = (∑ i, v i) - T := by
  classical
  let Q : ℝ := ∑ i, v i
  let L : ℝ := ∑ i, lam i
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ => hlam i)
  have hQT : T ≤ Q := hTv
  have hTL : -L ≤ T := hT
  by_cases heq : Q = T
  · refine ⟨v, hv, fun _ => le_rfl, heq, ?_⟩
    simp [heq, Q]
  · have h1 : -L ≤ Q := by
      have hneg : (∑ i, -lam i) = -L := by rw [Finset.sum_neg_distrib]
      have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (hv i).1)
      rwa [hneg] at hs
    have hden : 0 < Q + L := by
      by_contra hn
      have hn' : Q + L ≤ 0 := le_of_not_gt hn
      have hQe : Q = -L := le_antisymm (by linarith) h1
      have hTe : T = Q := by linarith
      exact heq hTe.symm
    let θ : ℝ := (Q - T) / (Q + L)
    have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hQT) hden.le
    have hθ1 : θ ≤ 1 := by
      dsimp [θ]
      apply (div_le_iff₀ hden).mpr
      linarith
    let z : ι → ℝ := fun i => v i - θ * (v i + lam i)
    have hzv (i : ι) : z i ≤ v i := by
      have hp := mul_nonneg hθ0 (by linarith [(hv i).1] : 0 ≤ v i + lam i)
      dsimp [z]
      linarith
    have hzb : InSymmetricBox lam z := by
      intro i
      constructor
      · have hp := mul_nonneg (by linarith : 0 ≤ 1 - θ)
          (by linarith [(hv i).1] : 0 ≤ v i + lam i)
        dsimp [z]
        nlinarith
      · exact (hzv i).trans (hv i).2
    have hsum : (∑ i, z i) = T := by
      have h1 : ∀ i : ι, z i = v i - θ * v i - θ * lam i := by
        intro i
        dsimp [z]
        ring
      have h2 : (∑ i, z i)
          = (∑ i, v i) - θ * (∑ i, v i) - θ * (∑ i, lam i) := by
        simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hQe : (∑ i, v i) = Q := rfl
      have hLe : (∑ i, lam i) = L := rfl
      rw [h2, hQe, hLe]
      dsimp only [θ]
      field_simp [ne_of_gt hden]
      ring
    refine ⟨z, hzb, hzv, hsum, ?_⟩
    calc
      (∑ i, |z i - v i|) = ∑ i, (v i - z i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_of_nonpos (sub_nonpos.mpr (hzv i))]
        ring
      _ = (∑ i, v i) - T := by rw [Finset.sum_sub_distrib, hsum]

/-- Move to any feasible coordinate sum with exactly the paid l1 displacement.
No coordinate width is enlarged, and zero widths are allowed. -/
theorem box_sum_adjust {ι : Type*} [Fintype ι]
    (lam v : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hv : InSymmetricBox lam v)
    (T : ℝ) (hTlo : -(∑ i, lam i) ≤ T) (hThi : T ≤ ∑ i, lam i) :
    ∃ z : ι → ℝ, InSymmetricBox lam z ∧ (∑ i, z i) = T ∧
      (∑ i, |z i - v i|) = |(∑ i, v i) - T| := by
  classical
  by_cases hTv : T ≤ ∑ i, v i
  · rcases box_sum_adjust_down lam v hlam hv T hTlo hTv with
      ⟨z, hzb, _, hsum, hdist⟩
    exact ⟨z, hzb, hsum, by rwa [abs_of_nonneg (sub_nonneg.mpr hTv)]⟩
  · have hvT : (∑ i, v i) ≤ T := le_of_not_ge hTv
    have hvn : InSymmetricBox lam (fun i => -v i) := by
      intro i
      constructor <;> linarith [(hv i).1, (hv i).2]
    have hTn : -(∑ i, lam i) ≤ -T := by linarith
    have hTvn : -T ≤ ∑ i, -v i := by
      rw [Finset.sum_neg_distrib]
      linarith
    rcases box_sum_adjust_down lam (fun i => -v i) hlam hvn (-T) hTn hTvn with
      ⟨z, hzb, _, hsum, hdist⟩
    refine ⟨fun i => -z i, ?_, ?_, ?_⟩
    · intro i
      constructor <;> linarith [(hzb i).1, (hzb i).2]
    · rw [Finset.sum_neg_distrib, hsum]
      ring
    · have habs : (∑ i, |-z i - v i|) = ∑ i, |z i - -v i| := by
        apply Finset.sum_congr rfl
        intro i _
        have he : -z i - v i = -(z i - -v i) := by ring
        rw [he, abs_neg]
      rw [habs, hdist, Finset.sum_neg_distrib,
        abs_of_nonpos (sub_nonpos.mpr hvT)]
      ring

/-- A genuine zero-sum physical box always admits a closest l1 projection. -/
theorem zero_sum_box_projection {ι : Type*} [Fintype ι]
    (lam v : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hv : InSymmetricBox lam v) :
    ∃ z : ι → ℝ, InSymmetricBox lam z ∧ (∑ i, z i) = 0 ∧
      (∑ i, |z i - v i|) = |∑ i, v i| := by
  have hL : 0 ≤ ∑ i, lam i := Finset.sum_nonneg (fun i _ => hlam i)
  simpa using box_sum_adjust lam v hlam hv 0 (by linarith) hL

def removeCoordinate {ι : Type*} [DecidableEq ι] (v : ι → ℝ) (i j : ι) : ℝ :=
  if j = i then 0 else v j

private theorem sum_removeCoordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (i : ι) :
    (∑ j, removeCoordinate v i j) = (∑ j, v j) - v i := by
  have hs : (∑ j, v j) = (∑ j, removeCoordinate v i j) + v i := by
    calc
      (∑ j, v j) = ∑ j, (removeCoordinate v i j + if j = i then v i else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i <;> simp [removeCoordinate, hj]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linarith

def TouchesBoxFace {ι : Type*} (lam z : ι → ℝ) : Prop := ∃ i, |z i| = lam i

/-- Exact paid projection from an upper endpoint. A dominant width uses the
opposite-corner section vertex, so this never assumes its original face meets
the zero-sum plane. `TouchesBoxFace` becomes the actual plane-section boundary
criterion in the positive-width double/triple cases. -/
theorem zero_sum_face_projection_upper {ι : Type*} [Fintype ι]
    (lam v : ι → ℝ) (hlam : ∀ j, 0 ≤ lam j) (hv : InSymmetricBox lam v)
    (i : ι) (hvi : v i = lam i) (hother : ∃ j, j ≠ i) :
    ∃ z : ι → ℝ, InSymmetricBox lam z ∧ (∑ j, z j) = 0 ∧
      (∑ j, |z j - v j|) = |∑ j, v j| ∧ TouchesBoxFace lam z := by
  classical
  let lam' : ι → ℝ := removeCoordinate lam i
  let v' : ι → ℝ := removeCoordinate v i
  have hlam' : ∀ j, 0 ≤ lam' j := by
    intro j
    by_cases hj : j = i <;> simp [lam', removeCoordinate, hj, hlam]
  have hv' : InSymmetricBox lam' v' := by
    intro j
    by_cases hj : j = i
    · simp [lam', v', removeCoordinate, hj]
    · simpa [lam', v', removeCoordinate, hj] using hv j
  have hM : 0 ≤ ∑ j, lam' j := Finset.sum_nonneg (fun j _ => hlam' j)
  by_cases hi : lam i ≤ ∑ j, lam' j
  · rcases box_sum_adjust lam' v' hlam' hv' (-lam i)
      (by linarith) (by linarith [hlam i]) with ⟨u, hub, hus, hud⟩
    have hui : u i = 0 := by
      have hu := hub i
      simp only [lam', removeCoordinate, ite_true, neg_zero] at hu
      linarith
    let z : ι → ℝ := fun j => u j + if j = i then lam i else 0
    have hzb : InSymmetricBox lam z := by
      intro j
      by_cases hj : j = i
      · subst j
        simp only [z, ite_true, hui, zero_add]
        constructor <;> linarith [hlam i]
      · simpa [z, lam', removeCoordinate, hj] using hub j
    have hzs : (∑ j, z j) = 0 := by
      dsimp [z]
      rw [Finset.sum_add_distrib, hus]
      simp
    have hzd : (∑ j, |z j - v j|) = |∑ j, v j| := by
      have hterm (j : ι) : |z j - v j| = |u j - v' j| := by
        by_cases hj : j = i
        · subst j
          simp [z, v', removeCoordinate, hui, hvi]
        · simp [z, v', removeCoordinate, hj]
      simp_rw [hterm]
      rw [hud]
      dsimp [v']
      rw [sum_removeCoordinate, hvi]
      congr 1
      ring
    refine ⟨z, hzb, hzs, hzd, i, ?_⟩
    simp [z, hui, abs_of_nonneg (hlam i)]
  · have hdom : (∑ j, lam' j) < lam i := lt_of_not_ge hi
    let M : ℝ := ∑ j, lam' j
    have hMv : -(∑ j, lam' j) ≤ ∑ j, v' j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro j _
      exact (hv' j).1
    have hQ : 0 < ∑ j, v j := by
      have hdom' : (∑ j, removeCoordinate lam i j) < lam i := hdom
      have hpoint : ∀ j, -removeCoordinate lam i j ≤ removeCoordinate v i j := by
        intro j
        by_cases hj : j = i
        · subst j
          show -(if i = i then (0 : ℝ) else lam i) ≤
            if i = i then (0 : ℝ) else v i
          simp
        · have hq1 : removeCoordinate lam i j = lam j := by
            simp [removeCoordinate, hj]
          have hq2 : removeCoordinate v i j = v j := by
            simp [removeCoordinate, hj]
          rw [hq1, hq2]
          exact (hv j).1
      have h1 : -(∑ j, removeCoordinate lam i j) ≤ ∑ j, removeCoordinate v i j := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum (fun j _ => hpoint j)
      have h2 : (∑ j, removeCoordinate v i j) = (∑ j, v j) - v i :=
        sum_removeCoordinate v i
      have h3 : -(∑ j, removeCoordinate lam i j) ≤ (∑ j, v j) - v i := by
        linarith
      rw [hvi] at h3
      linarith
    let z : ι → ℝ := fun j => if j = i then M else -lam j
    have hzb : InSymmetricBox lam z := by
      intro j
      by_cases hj : j = i
      · subst j
        simp only [z, ite_true]
        dsimp [M]
        constructor <;> linarith [hlam i]
      · simp only [z, if_neg hj]
        constructor
        · exact le_rfl
        · linarith [hlam j]
    have hzv (j : ι) : z j ≤ v j := by
      by_cases hj : j = i
      · subst j
        simpa [z, M, hvi] using hdom.le
      · simpa [z, hj] using (hv j).1
    have hzs : (∑ j, z j) = 0 := by
      have hterm (j : ι) : z j = -lam' j + if j = i then M else 0 := by
        by_cases hj : j = i <;> simp [z, lam', removeCoordinate, hj]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      simp [M]
    have hzd : (∑ j, |z j - v j|) = |∑ j, v j| := by
      calc
        (∑ j, |z j - v j|) = ∑ j, (v j - z j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_of_nonpos (sub_nonpos.mpr (hzv j))]
          ring
        _ = ∑ j, v j := by rw [Finset.sum_sub_distrib, hzs]; ring
        _ = |∑ j, v j| := (abs_of_nonneg hQ.le).symm
    obtain ⟨j, hji⟩ := hother
    refine ⟨z, hzb, hzs, hzd, j, ?_⟩
    simp [z, hji, abs_of_nonneg (hlam j)]

/-- Endpoint reflection covers both actual tail signs with the SAME payment. -/
theorem zero_sum_face_projection {ι : Type*} [Fintype ι]
    (lam v : ι → ℝ) (hlam : ∀ j, 0 ≤ lam j) (hv : InSymmetricBox lam v)
    (i : ι) (hvi : |v i| = lam i) (hother : ∃ j, j ≠ i) :
    ∃ z : ι → ℝ, InSymmetricBox lam z ∧ (∑ j, z j) = 0 ∧
      (∑ j, |z j - v j|) = |∑ j, v j| ∧ TouchesBoxFace lam z := by
  by_cases hpos : 0 ≤ v i
  · rw [abs_of_nonneg hpos] at hvi
    exact zero_sum_face_projection_upper lam v hlam hv i hvi hother
  · have hneg : v i ≤ 0 := le_of_not_ge hpos
    have hvin : -v i = lam i := by rwa [abs_of_nonpos hneg] at hvi
    have hvn : InSymmetricBox lam (fun j => -v j) := by
      intro j
      constructor <;> linarith [(hv j).1, (hv j).2]
    rcases zero_sum_face_projection_upper lam (fun j => -v j) hlam hvn i hvin hother
      with ⟨u, hub, hus, hud, j, hj⟩
    refine ⟨fun j => -u j, ?_, ?_, ?_, j, ?_⟩
    · intro k
      constructor <;> linarith [(hub k).1, (hub k).2]
    · rw [Finset.sum_neg_distrib, hus]
      simp
    · have he (k : ι) : |-u k - v k| = |u k - -v k| := by
        rw [show -u k - v k = -(u k - -v k) by ring, abs_neg]
      simp_rw [he]
      rw [hud, Finset.sum_neg_distrib, abs_neg]
    · simpa only [abs_neg] using hj

theorem physical_triangle {d : ℕ} (a b c : Point d) :
    l1dist a c ≤ l1dist a b + l1dist b c := by
  unfold l1dist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  simpa only [sub_add_sub_cancel] using abs_add_le (a k - b k) (b k - c k)

private theorem physical_eq_of_distance_zero {d : ℕ} {a b : Point d}
    (h : l1dist a b = 0) : a = b := by
  funext k
  have hk := coordinate_distance_le a b k
  rw [h] at hk
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hk (abs_nonneg _)))

def linePoint {d : ℕ} (a b : Point d) (θ : ℝ) : Point d :=
  fun k => a k + θ * (b k - a k)

theorem linePoint_distance {d : ℕ} (a b : Point d) (θ φ : ℝ) :
    l1dist (linePoint a b θ) (linePoint a b φ) = |θ - φ| * l1dist a b := by
  unfold l1dist
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have he : linePoint a b θ k - linePoint a b φ k =
      (θ - φ) * (b k - a k) := by unfold linePoint; ring
  rw [he, abs_mul, abs_sub_comm (b k) (a k)]

/-- An elementary interval path with a budget for literal physical l1 chords.
No normed-space isometry, curve-length axiom or perimeter premise is used. -/
structure PhysicalPath {d : ℕ} (a b : Point d) where
  budget : ℝ
  nonneg : 0 ≤ budget
  point : ℝ → Point d
  at_zero : point 0 = a
  at_budget : point budget = b
  chord : ∀ s t, 0 ≤ s → s ≤ t → t ≤ budget →
    l1dist (point s) (point t) ≤ t - s

namespace PhysicalPath

def Covers {d : ℕ} {a b : Point d} (p : PhysicalPath a b) (z : Point d) : Prop :=
  ∃ s, 0 ≤ s ∧ s ≤ p.budget ∧ p.point s = z

noncomputable def straight {d : ℕ} (a b : Point d) : PhysicalPath a b := by
  have hp0 : linePoint a b 0 = a := by
    funext k
    simp [linePoint]
  refine ⟨l1dist a b, l1dist_nonneg a b, fun s => linePoint a b (s / l1dist a b),
    ?_, ?_, ?_⟩
  · show linePoint a b ((0 : ℝ) / l1dist a b) = a
    rw [zero_div, hp0]
  · by_cases hz : l1dist a b = 0
    · have hab : a = b := physical_eq_of_distance_zero hz
      show linePoint a b (l1dist a b / l1dist a b) = b
      rw [hz, zero_div, hp0, hab]
    · show linePoint a b (l1dist a b / l1dist a b) = b
      rw [div_self hz]
      funext k
      simp [linePoint]
  · intro s t hs hst ht
    by_cases hz : l1dist a b = 0
    · rw [hz]
      simp only [div_zero, hp0, l1dist_self]
      linarith
    · have hLp : 0 < l1dist a b := lt_of_le_of_ne (l1dist_nonneg a b) (Ne.symm hz)
      rw [linePoint_distance]
      have hdiv : s / l1dist a b ≤ t / l1dist a b :=
        div_le_div_of_nonneg_right hst hLp.le
      rw [abs_of_nonpos (sub_nonpos.mpr hdiv)]
      have he : -(s / l1dist a b - t / l1dist a b) * l1dist a b = t - s := by
        field_simp [hz]
        ring
      rw [he]

@[simp] theorem straight_budget {d : ℕ} (a b : Point d) :
    (straight a b).budget = l1dist a b := rfl

theorem straight_covers {d : ℕ} (a b : Point d) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (straight a b).Covers (linePoint a b θ) := by
  classical
  by_cases hz : l1dist a b = 0
  · have hab := physical_eq_of_distance_zero hz
    subst b
    refine ⟨0, le_rfl, (straight a a).nonneg, ?_⟩
    rw [(straight a a).at_zero]
    funext k
    simp [linePoint]
  · refine ⟨θ * l1dist a b, mul_nonneg hθ0 (l1dist_nonneg a b), ?_, ?_⟩
    · rw [straight_budget]
      nlinarith [hθ1, l1dist_nonneg a b]
    · show linePoint a b (θ * l1dist a b / l1dist a b) = linePoint a b θ
      simp [mul_div_cancel_right₀ _ hz]

noncomputable def concat {d : ℕ} {a b c : Point d}
    (p : PhysicalPath a b) (q : PhysicalPath b c) : PhysicalPath a c := by
  classical
  let f : ℝ → Point d := fun s => if s ≤ p.budget then p.point s
    else q.point (s - p.budget)
  refine ⟨p.budget + q.budget, add_nonneg p.nonneg q.nonneg, f, ?_, ?_, ?_⟩
  · simp [f, p.nonneg, p.at_zero]
  · by_cases hq : q.budget = 0
    · have hbc : b = c := by simpa [hq, q.at_zero] using q.at_budget
      simpa [f, hq, p.at_budget] using hbc
    · have hqp : 0 < q.budget := lt_of_le_of_ne q.nonneg (Ne.symm hq)
      have hn : ¬p.budget + q.budget ≤ p.budget := by linarith
      simp [f, hn, q.at_budget]
  · intro s t hs hst ht
    by_cases hsP : s ≤ p.budget
    · by_cases htP : t ≤ p.budget
      · simpa [f, hsP, htP] using p.chord s t hs hst htP
      · have htp : 0 ≤ t - p.budget := by linarith
        have htq : t - p.budget ≤ q.budget := by linarith
        have hleft := p.chord s p.budget hs hsP le_rfl
        have hright := q.chord 0 (t - p.budget) le_rfl htp htq
        have htri := physical_triangle (p.point s) b (q.point (t - p.budget))
        rw [p.at_budget] at hleft
        rw [q.at_zero] at hright
        simp only [sub_zero] at hright
        dsimp [f]
        rw [if_pos hsP, if_neg htP]
        linarith
    · have htP : ¬t ≤ p.budget := by linarith
      have hsp : 0 ≤ s - p.budget := by linarith
      have hsqt : s - p.budget ≤ t - p.budget := by linarith
      have htq : t - p.budget ≤ q.budget := by linarith
      have hh := q.chord (s - p.budget) (t - p.budget) hsp hsqt htq
      dsimp [f]
      rw [if_neg hsP, if_neg htP]
      linarith

@[simp] theorem concat_budget {d : ℕ} {a b c : Point d}
    (p : PhysicalPath a b) (q : PhysicalPath b c) :
    (p.concat q).budget = p.budget + q.budget := rfl

theorem concat_covers_left {d : ℕ} {a b c z : Point d}
    (p : PhysicalPath a b) (q : PhysicalPath b c) (hz : p.Covers z) :
    (p.concat q).Covers z := by
  classical
  obtain ⟨s, hs, hsp, hpz⟩ := hz
  refine ⟨s, hs, ?_, ?_⟩
  · rw [concat_budget]
    linarith [q.nonneg]
  · change (if s ≤ p.budget then p.point s else q.point (s - p.budget)) = z
    simpa [hsp] using hpz

theorem concat_covers_right {d : ℕ} {a b c z : Point d}
    (p : PhysicalPath a b) (q : PhysicalPath b c) (hz : q.Covers z) :
    (p.concat q).Covers z := by
  classical
  obtain ⟨s, hs, hsq, hqz⟩ := hz
  refine ⟨p.budget + s, add_nonneg p.nonneg hs, ?_, ?_⟩
  · rw [concat_budget]
    linarith
  · change (if p.budget + s ≤ p.budget then p.point (p.budget + s)
      else q.point (p.budget + s - p.budget)) = z
    by_cases hz : s = 0
    · subst s
      simpa [p.at_budget, q.at_zero] using hqz
    · have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
      have hn : ¬p.budget + s ≤ p.budget := by linarith
      simpa [hn] using hqz

end PhysicalPath

private theorem ordered_scalar_interpolation {a b z : ℝ} (hab : a ≤ b)
    (haz : a ≤ z) (hzb : z ≤ b) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ a + θ * (b - a) = z := by
  by_cases heq : a = b
  · refine ⟨0, le_rfl, by norm_num, ?_⟩
    linarith
  · have hpos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq)
    refine ⟨(z - a) / (b - a), div_nonneg (by linarith) hpos.le, ?_, ?_⟩
    · apply (div_le_iff₀ hpos).mpr
      linarith
    · field_simp [ne_of_gt hpos]
      ring

theorem scalar_between_interpolation {a b z : ℝ}
    (hz : min a b ≤ z ∧ z ≤ max a b) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ a + θ * (b - a) = z := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab] at hz
    exact ordered_scalar_interpolation hab hz.1 hz.2
  · rw [min_eq_right hba, max_eq_left hba] at hz
    obtain ⟨θ, hθ0, hθ1, hθ⟩ := ordered_scalar_interpolation hba hz.1 hz.2
    refine ⟨1 - θ, by linarith, by linarith, ?_⟩
    nlinarith

/-- Two actual coordinates determine a zero-sum point in three coordinates. -/
theorem zero_sum_three_eq_of_two (a b : Point 3)
    (ha : (∑ k, a k) = 0) (hb : (∑ k, b k) = 0)
    (i j : Fin 3) (hij : i ≠ j) (hi : a i = b i) (hj : a j = b j) : a = b := by
  norm_num [Fin.sum_univ_succ] at ha hb
  fin_cases i <;> fin_cases j <;> simp_all <;>
    funext k <;> fin_cases k <;> simp_all <;> linarith

/-- Coverage of an ACTUAL saturated three-coordinate face by its straight
edge; a degenerate edge is included by scalar interpolation at budget zero. -/
theorem zero_sum_three_edge_covers (a b z : Point 3)
    (ha : (∑ k, a k) = 0) (hb : (∑ k, b k) = 0) (hz : (∑ k, z k) = 0)
    (i j : Fin 3) (hij : i ≠ j) (hfixed : a i = b i) (hzi : z i = a i)
    (hzj : min (a j) (b j) ≤ z j ∧ z j ≤ max (a j) (b j)) :
    (PhysicalPath.straight a b).Covers z := by
  obtain ⟨θ, hθ0, hθ1, hθj⟩ := scalar_between_interpolation hzj
  have hsum : (∑ k, linePoint a b θ k) = 0 := by
    simp only [linePoint, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ha, hb]
    ring
  have heq : linePoint a b θ = z := by
    apply zero_sum_three_eq_of_two _ _ hsum hz i j hij
    · dsimp [linePoint]
      rw [← hfixed]
      simpa using hzi.symm
    · exact hθj
  rw [← heq]
  exact PhysicalPath.straight_covers a b θ hθ0 hθ1

def nextFour (i : Fin 4) : Fin 4 := ⟨(i.val + 1) % 4, Nat.mod_lt _ (by decide)⟩
def nextSix (i : Fin 6) : Fin 6 := ⟨(i.val + 1) % 6, Nat.mod_lt _ (by decide)⟩

noncomputable def polygonFour {d : ℕ} (v : Fin 4 → Point d) :
    PhysicalPath (v 0) (v 0) :=
  (((PhysicalPath.straight (v 0) (v 1)).concat
    (PhysicalPath.straight (v 1) (v 2))).concat
    (PhysicalPath.straight (v 2) (v 3))).concat
    (PhysicalPath.straight (v 3) (v 0))

noncomputable def polygonSix {d : ℕ} (v : Fin 6 → Point d) :
    PhysicalPath (v 0) (v 0) :=
  (((((PhysicalPath.straight (v 0) (v 1)).concat
    (PhysicalPath.straight (v 1) (v 2))).concat
    (PhysicalPath.straight (v 2) (v 3))).concat
    (PhysicalPath.straight (v 3) (v 4))).concat
    (PhysicalPath.straight (v 4) (v 5))).concat
    (PhysicalPath.straight (v 5) (v 0))

theorem polygonFour_budget {d : ℕ} (v : Fin 4 → Point d) :
    (polygonFour v).budget = ∑ i, l1dist (v i) (v (nextFour i)) := by
  simp [polygonFour, Fin.sum_univ_succ, nextFour]
  ring

theorem polygonSix_budget {d : ℕ} (v : Fin 6 → Point d) :
    (polygonSix v).budget = ∑ i, l1dist (v i) (v (nextSix i)) := by
  simp [polygonSix, Fin.sum_univ_succ, nextSix]
  ring

theorem polygonFour_covers_edge {d : ℕ} (v : Fin 4 → Point d)
    (i : Fin 4) (z : Point d)
    (hz : (PhysicalPath.straight (v i) (v (nextFour i))).Covers z) :
    (polygonFour v).Covers z := by
  fin_cases i
  · apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    simpa [nextFour] using hz
  · apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_right
    simpa [nextFour] using hz
  · apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_right
    simpa [nextFour] using hz
  · apply PhysicalPath.concat_covers_right
    simpa [nextFour] using hz

theorem polygonSix_covers_edge {d : ℕ} (v : Fin 6 → Point d)
    (i : Fin 6) (z : Point d)
    (hz : (PhysicalPath.straight (v i) (v (nextSix i))).Covers z) :
    (polygonSix v).Covers z := by
  fin_cases i
  · apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    simpa [nextSix] using hz
  · apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_right
    simpa [nextSix] using hz
  · apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_right
    simpa [nextSix] using hz
  · apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_right
    simpa [nextSix] using hz
  · apply PhysicalPath.concat_covers_left
    apply PhysicalPath.concat_covers_right
    simpa [nextSix] using hz
  · apply PhysicalPath.concat_covers_right
    simpa [nextSix] using hz

def formCoefficient (plus : Bool) (index slot : Fin 4) : ℝ :=
  if plus then (if slot = index then 2 else 0)
  else (if slot = index then -1 else 1)

def formValue (plus : Bool) (index : Fin 4) (A : Fin 4 → ℝ) : ℝ :=
  ∑ h, formCoefficient plus index h * A h

noncomputable def agreementMass (A : Fin 4 → ℝ) : ℝ := A 0 + A 1 + A 2 + A 3

noncomputable def agreementDisplacement (A : Fin 4 → ℝ) : ℝ :=
  (|A 0 + A 1 - A 2 - A 3| + |A 0 - A 1 + A 2 - A 3| +
    |A 0 - A 1 - A 2 + A 3|) / 2

noncomputable def agreementBudget (A : Fin 4 → ℝ) : ℝ :=
  agreementMass A / 2 + agreementDisplacement A

@[simp] theorem formValue_plus (i : Fin 4) (A : Fin 4 → ℝ) :
    formValue true i A = 2 * A i := by
  fin_cases i <;> simp [formValue, formCoefficient, Fin.sum_univ_succ]

@[simp] theorem formValue_minus (i : Fin 4) (A : Fin 4 → ℝ) :
    formValue false i A = agreementMass A - 2 * A i := by
  fin_cases i <;> simp [formValue, formCoefficient, agreementMass,
    Fin.sum_univ_succ] <;> ring

/-- The paid tail mass and projection displacement have ONE jointly maximizing
indexed form. This holds for arbitrary real vectors, including every tie. -/
theorem agreementBudget_has_form (A : Fin 4 → ℝ) :
    ∃ p : Bool, ∃ i : Fin 4, formValue p i A = agreementBudget A := by
  let u := A 0 + A 1 - A 2 - A 3
  let v := A 0 - A 1 + A 2 - A 3
  let w := A 0 - A 1 - A 2 + A 3
  by_cases hu : 0 ≤ u <;> by_cases hv : 0 ≤ v <;> by_cases hw : 0 ≤ w
  · refine ⟨true, 0, ?_⟩
    rw [formValue_plus]
    change 2 * A 0 = agreementMass A / 2 + (|u| + |v| + |w|) / 2
    rw [abs_of_nonneg hu, abs_of_nonneg hv, abs_of_nonneg hw]
    dsimp [u, v, w, agreementMass]
    ring
  · refine ⟨false, 3, ?_⟩
    rw [formValue_minus]
    change agreementMass A - 2 * A 3 = agreementMass A / 2 + (|u| + |v| + |w|) / 2
    rw [abs_of_nonneg hu, abs_of_nonneg hv, abs_of_nonpos (le_of_not_ge hw)]
    dsimp [u, v, w, agreementMass]
    ring
  · refine ⟨false, 2, ?_⟩
    rw [formValue_minus]
    change agreementMass A - 2 * A 2 = agreementMass A / 2 + (|u| + |v| + |w|) / 2
    rw [abs_of_nonneg hu, abs_of_nonpos (le_of_not_ge hv), abs_of_nonneg hw]
    dsimp [u, v, w, agreementMass]
    ring
  · refine ⟨true, 1, ?_⟩
    rw [formValue_plus]
    change 2 * A 1 = agreementMass A / 2 + (|u| + |v| + |w|) / 2
    rw [abs_of_nonneg hu, abs_of_nonpos (le_of_not_ge hv),
      abs_of_nonpos (le_of_not_ge hw)]
    dsimp [u, v, w, agreementMass]
    ring
  · refine ⟨false, 1, ?_⟩
    rw [formValue_minus]
    change agreementMass A - 2 * A 1 = agreementMass A / 2 + (|u| + |v| + |w|) / 2
    rw [abs_of_nonpos (le_of_not_ge hu), abs_of_nonneg hv, abs_of_nonneg hw]
    dsimp [u, v, w, agreementMass]
    ring
  · refine ⟨true, 2, ?_⟩
    rw [formValue_plus]
    change 2 * A 2 = agreementMass A / 2 + (|u| + |v| + |w|) / 2
    rw [abs_of_nonpos (le_of_not_ge hu), abs_of_nonneg hv,
      abs_of_nonpos (le_of_not_ge hw)]
    dsimp [u, v, w, agreementMass]
    ring
  · refine ⟨true, 3, ?_⟩
    rw [formValue_plus]
    change 2 * A 3 = agreementMass A / 2 + (|u| + |v| + |w|) / 2
    rw [abs_of_nonpos (le_of_not_ge hu), abs_of_nonpos (le_of_not_ge hv),
      abs_of_nonneg hw]
    dsimp [u, v, w, agreementMass]
    ring
  · refine ⟨false, 0, ?_⟩
    rw [formValue_minus]
    change agreementMass A - 2 * A 0 = agreementMass A / 2 + (|u| + |v| + |w|) / 2
    rw [abs_of_nonpos (le_of_not_ge hu), abs_of_nonpos (le_of_not_ge hv),
      abs_of_nonpos (le_of_not_ge hw)]
    dsimp [u, v, w, agreementMass]
    ring

theorem formValue_le_agreementBudget (p : Bool) (i : Fin 4) (A : Fin 4 → ℝ) :
    formValue p i A ≤ agreementBudget A := by
  have hu := le_abs_self (A 0 + A 1 - A 2 - A 3)
  have hnu := neg_le_abs (A 0 + A 1 - A 2 - A 3)
  have hv := le_abs_self (A 0 - A 1 + A 2 - A 3)
  have hnv := neg_le_abs (A 0 - A 1 + A 2 - A 3)
  have hw := le_abs_self (A 0 - A 1 - A 2 + A 3)
  have hnw := neg_le_abs (A 0 - A 1 - A 2 + A 3)
  cases p <;> fin_cases i <;>
    simp [agreementBudget, agreementDisplacement, agreementMass] <;> linarith

def slotVertexCap (c d : ℝ) : ℝ := max 0 (max c (max d (c + d - 2)))

private theorem scalar_slot_le {b u v c d M : ℝ}
    (hb : 0 ≤ b) (hu0 : 0 ≤ u) (hub : u ≤ b)
    (hv0 : 0 ≤ v) (hvb : v ≤ b)
    (hM0 : 0 ≤ M) (hMc : c * b ≤ M) (hMd : d * b ≤ M)
    (hMcd : (c + d - 2) * b ≤ M) :
    c * u + d * v - 2 * max 0 (u + v - b) ≤ M := by
  by_cases hb0 : b = 0
  · have hu : u = 0 := by linarith
    have hv : v = 0 := by linarith
    simpa [hb0, hu, hv] using hM0
  · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    by_cases huv : u + v ≤ b
    · rw [max_eq_left (by linarith : u + v - b ≤ 0)]
      have h1 := mul_le_mul_of_nonneg_left hMc hu0
      have h2 := mul_le_mul_of_nonneg_left hMd hv0
      have h3 := mul_nonneg hM0 (by linarith : 0 ≤ b - u - v)
      nlinarith
    · rw [max_eq_right (by linarith : 0 ≤ u + v - b)]
      have h1 := mul_le_mul_of_nonneg_left hMc (by linarith : 0 ≤ b - v)
      have h2 := mul_le_mul_of_nonneg_left hMd (by linarith : 0 ≤ b - u)
      have h3 := mul_le_mul_of_nonneg_left hMcd
        (by linarith : 0 ≤ u + v - b)
      have he :
          (b - v) * (c * b) + (b - u) * (d * b) +
            (u + v - b) * ((c + d - 2) * b) =
          b * (c * u + d * v - 2 * (u + v - b)) := by ring
      nlinarith

theorem scalar_slot_le_vertex_cap {b u v c d : ℝ}
    (hb : 0 ≤ b) (hu0 : 0 ≤ u) (hub : u ≤ b)
    (hv0 : 0 ≤ v) (hvb : v ≤ b) :
    c * u + d * v - 2 * max 0 (u + v - b) ≤ b * slotVertexCap c d := by
  apply scalar_slot_le hb hu0 hub hv0 hvb
  · exact mul_nonneg hb (le_max_left _ _)
  · have h : c ≤ slotVertexCap c d :=
      (le_max_left _ _).trans (le_max_right _ _)
    simpa [mul_comm] using mul_le_mul_of_nonneg_right h hb
  · have h : d ≤ slotVertexCap c d :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    simpa [mul_comm] using mul_le_mul_of_nonneg_right h hb
  · have h : c + d - 2 ≤ slotVertexCap c d :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    simpa [mul_comm] using mul_le_mul_of_nonneg_right h hb

def formPairCap (p q : Bool) (i j : Fin 4) : ℝ :=
  if i = j then (if p then (if q then 2 else 5) else (if q then 5 else 3))
  else 4

set_option maxHeartbeats 4000000 in
private theorem coefficient_caps_sum (p q : Bool) (i j : Fin 4) :
    (∑ h, slotVertexCap (formCoefficient p i h) (formCoefficient q j h)) =
      formPairCap p q i j := by
  cases p <;> cases q <;> fin_cases i <;> fin_cases j <;>
    norm_num [formCoefficient, slotVertexCap, formPairCap, Fin.sum_univ_succ]

/-- The full tied maximizing-form pair table, proved slot by slot. -/
theorem form_pair_bound {b : ℝ} (hb : 0 ≤ b)
    (A B : Fin 4 → ℝ) (hA : ∀ h, 0 ≤ A h ∧ A h ≤ b)
    (hB : ∀ h, 0 ≤ B h ∧ B h ≤ b)
    (p q : Bool) (i j : Fin 4) :
    formValue p i A + formValue q j B -
        2 * (∑ h, max 0 (A h + B h - b)) ≤ b * formPairCap p q i j := by
  calc
    _ = ∑ h, (formCoefficient p i h * A h + formCoefficient q j h * B h -
        2 * max 0 (A h + B h - b)) := by
      simp only [formValue, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
    _ ≤ ∑ h, b * slotVertexCap (formCoefficient p i h)
        (formCoefficient q j h) := by
      apply Finset.sum_le_sum
      intro h _
      exact scalar_slot_le_vertex_cap hb (hA h).1 (hA h).2 (hB h).1 (hB h).2
    _ = b * formPairCap p q i j := by
      rw [← Finset.mul_sum, coefficient_caps_sum]

def nextSeven (i : Fin 7) : Fin 7 :=
  ⟨(i.val + 1) % 7, Nat.mod_lt _ (by decide)⟩

/-- Sort parameters of the SAME seven points on an actual closed physical
tour. Its six forward budgets telescope; the closing chord passes through the
common endpoint. Repeated parameters and zero-length polygon edges are allowed. -/
theorem seven_cycle_of_closed_path {d : ℕ} {a : Point d}
    (path : PhysicalPath a a) (z : Fin 7 → Point d)
    (hcover : ∀ i, path.Covers (z i)) :
    ∃ σ : Equiv.Perm (Fin 7),
      (∑ i, l1dist (z (σ i)) (z (σ (nextSeven i)))) ≤ path.budget := by
  classical
  unfold PhysicalPath.Covers at hcover
  choose t ht0 htP htz using hcover
  let σ : Equiv.Perm (Fin 7) := actualOrder t
  have hm : Monotone (fun i => t (σ i)) := actualOrder_monotone t
  have hstep (i j : Fin 7) (hij : i ≤ j) :
      l1dist (z (σ i)) (z (σ j)) ≤ t (σ j) - t (σ i) := by
    simpa only [htz] using path.chord (t (σ i)) (t (σ j))
      (ht0 (σ i)) (hm hij) (htP (σ j))
  have h01 := hstep 0 1 (by decide)
  have h12 := hstep 1 2 (by decide)
  have h23 := hstep 2 3 (by decide)
  have h34 := hstep 3 4 (by decide)
  have h45 := hstep 4 5 (by decide)
  have h56 := hstep 5 6 (by decide)
  have hlast := path.chord (t (σ 6)) path.budget (ht0 (σ 6))
    (htP (σ 6)) le_rfl
  have hfirst := path.chord 0 (t (σ 0)) le_rfl (ht0 (σ 0)) (htP (σ 0))
  rw [path.at_budget, htz] at hlast
  rw [path.at_zero, htz] at hfirst
  have hclosing : l1dist (z (σ 6)) (z (σ 0)) ≤
      path.budget - t (σ 6) + t (σ 0) := by
    have hh := physical_triangle (z (σ 6)) a (z (σ 0))
    linarith
  refine ⟨σ, ?_⟩
  norm_num [Fin.sum_univ_succ, nextSeven]
  linarith

private theorem odd_seven_same_type :
    ∀ t : Fin 7 → Bool, ∃ i, t i = t (nextSeven i) := by
  set_option maxRecDepth 20000 in
  set_option maxHeartbeats 4000000 in
  decide

private theorem cycle_second_index_change (u : Fin 7 → Fin 4) (e : Fin 7)
    (hne : u e ≠ u (nextSeven e)) :
    ∃ f, f ≠ e ∧ u f ≠ u (nextSeven f) := by
  set_option maxRecDepth 20000 in
  set_option maxHeartbeats 4000000 in
  by_contra h
  have hall : ∀ j, j ≠ e → u j = u (nextSeven j) := by
    intro j hj
    by_contra hne'
    exact h ⟨j, hj, hne'⟩
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  have h3 := hall 3
  have h4 := hall 4
  have h5 := hall 5
  have h6 := hall 6
  fin_cases e <;> norm_num [nextSeven] at h0 h1 h2 h3 h4 h5 h6 hne <;> simp_all

/-- The seven-cycle cap for one consistently chosen form and index at each
node. The order is arbitrary; no independent edgewise choice is permitted. -/
theorem odd_cycle_cap33 {b : ℝ} (hb : 0 ≤ b)
    (t : Fin 7 → Bool) (u : Fin 7 → Fin 4) (w : Fin 7 → ℝ)
    (hbase : ∀ i, w i ≤ 5 * b)
    (hagree : ∀ i, t i = t (nextSeven i) → u i = u (nextSeven i) → w i ≤ 3 * b)
    (hchange : ∀ i, u i ≠ u (nextSeven i) → w i ≤ 4 * b) :
    (∑ i, w i) ≤ 33 * b := by
  classical
  obtain ⟨e, he⟩ := odd_seven_same_type t
  by_cases hue : u e = u (nextSeven e)
  · calc
      (∑ i, w i) ≤ ∑ i : Fin 7, (5 * b - if i = e then 2 * b else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hie : i = e
        · subst i
          simp only [ite_true]
          linarith [hagree e he hue]
        · simpa [hie] using hbase i
      _ = 33 * b := by simp [Finset.sum_sub_distrib]; ring
  · obtain ⟨f, hfe, huf⟩ := cycle_second_index_change u e hue
    calc
      (∑ i, w i) ≤ ∑ i : Fin 7,
          (5 * b - (if i = e then b else 0) - (if i = f then b else 0)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hie : i = e
        · subst i
          have hef : e ≠ f := Ne.symm hfe
          simp only [ite_true, if_neg hef]
          linarith [hchange e hue]
        · by_cases hif : i = f
          · subst i
            simp only [if_neg hfe, ite_true]
            linarith [hchange f huf]
          · simpa [hie, hif] using hbase i
      _ = 33 * b := by simp [Finset.sum_sub_distrib]; ring

end QuartetGeometry
end Kusner5
