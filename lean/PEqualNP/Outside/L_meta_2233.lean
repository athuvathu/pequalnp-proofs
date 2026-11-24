import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma osSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [orStep]
      omega

lemma osStep_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (k : ℕ) (hk : k < cs.length) :
    (orStep n cs g).getD k [] = cs.getD k [] := by
  simp only [orStep, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hk]

lemma osStep_gt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (k : ℕ) (hk : cs.length < k) :
    (orStep n cs g).getD k [] = [] := by
  simp only [orStep, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega)]
  rfl

lemma osStep_mem (n : ℕ) (cs : List (List ℕ)) (g : Gate) (i : ℕ) :
    i ∈ (orStep n cs g).getD cs.length [] ↔
      i = cs.length ∨ (g.op = GateOp.or ∧ ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧
        i ∈ cs.getD (w - n) []) := by
  simp only [orStep, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_cons]
  by_cases hop : g.op = GateOp.or
  · rw [if_pos hop]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · rintro (h | ⟨_, w, hw, h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
  · rw [if_neg hop]
    simp only [List.not_mem_nil, or_false]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨h, _⟩)
      · exact h
      · exact absurd h hop

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep n) []).length = gs.length := by
        rw [osSets_len]; simp
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [osStep_lt n _ g j (by omega), ih i j, e1]
        constructor
        · rintro ⟨_, h3 | ⟨hop, w, hw, h1, h2, h3⟩⟩
          · exact ⟨by simp; omega, Or.inl h3⟩
          · refine ⟨by simp; omega, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [osStep_lt n _ g (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨hop, w, hw, h1, h2, h3⟩⟩
          · exact ⟨h, Or.inl h3⟩
          · refine ⟨h, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [osStep_lt n _ g (w - n) (by omega)] at h3
            exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have hm := osStep_mem n (gs.foldl (orStep n) []) g i
        rw [hlen] at hm
        rw [hm, e1]
        constructor
        · rintro (h3 | ⟨hop, w, hw, h1, h2, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [osStep_lt n _ g (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨hop, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [osStep_lt n _ g (w - n) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · rw [osStep_gt n _ g j (by omega)]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩
          simp at h0
          omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (j g : ℕ) :
    OrReaches n C (n + j) g ↔ j < C.gates.length ∧ (g = j ∨
      ((gateAt C j).op = GateOp.or ∧ ∃ w ∈ (gateAt C j).inputs, w < n + j ∧
        OrReaches n C w g)) := by
  have h := orSets_char n C.gates g j
  unfold OrReaches orSets gateAt
  have e : n + j - n = j := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, h0, h3 | ⟨hop, w, hw, h1, h2, h3⟩⟩
    · exact ⟨h0, Or.inl h3⟩
    · exact ⟨h0, Or.inr ⟨hop, w, hw, h2, h1, h3⟩⟩
  · rintro ⟨h0, h3 | ⟨hop, w, hw, h2, h1, h3⟩⟩
    · exact ⟨by omega, h0, Or.inl h3⟩
    · exact ⟨by omega, h0, Or.inr ⟨hop, w, hw, h1, h2, h3⟩⟩

lemma output_bounds (n : ℕ) (C : Circuit) (x : ℕ) (h : OrToOutput n C x) :
    n ≤ C.output ∧ C.output < n + C.gates.length := by
  unfold OrToOutput OrReaches at h
  refine ⟨h.1, ?_⟩
  have hlen : (orSets n C).length = C.gates.length := by
    rw [orSets, osSets_len]
    simp
  by_contra hge
  have hget : (orSets n C).getD (C.output - n) [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · simp [hlen]
      omega
  rw [hget] at h
  simp at h

lemma exists_reader (n : ℕ) (C : Circuit) (x : ℕ) :
    ∀ w, n ≤ w → w < n + C.gates.length → OrReaches n C w x → w ≠ n + x →
      ∃ h : ℕ, h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
        n + x ∈ (gateAt C h).inputs ∧ OrReaches n C w h := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
      intro hnw hwl hwx hne
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      rw [orReaches_iff] at hwx
      obtain ⟨hj, hcase | ⟨hop, v, hv, hvl, hvx⟩⟩ := hwx
      · subst x
        exact (hne rfl).elim
      · by_cases hvx0 : v = n + x
        · refine ⟨j, hj, hop, ?_, ?_⟩
          · simpa [hvx0] using hv
          · rw [orReaches_iff]
            exact ⟨hj, Or.inl rfl⟩
        · obtain ⟨h, hhj, hop_h, hin_h, hor_h⟩ :=
            ih v hvl hvx.1 (by omega) hvx hvx0
          refine ⟨h, hhj, hop_h, hin_h, ?_⟩
          rw [orReaches_iff]
          exact ⟨hj, Or.inr ⟨hop, v, hv, hvl, hor_h⟩⟩

lemma mem_inputs_pos (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j w : ℕ)
    (hj : j < C.gates.length) (hin : w ∈ (gateAt C j).inputs) :
    ∃ p : Fin 2, (gateAt C j).inputs.getD p.1 0 = w := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ hmem
  obtain ⟨p, hplen, hp⟩ := List.mem_iff_getElem.mp hin
  refine ⟨⟨p, by omega⟩, ?_⟩
  rw [List.getD_eq_getElem _ _ hplen]
  exact hp

end PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Outside.L_meta_2233

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hAO hF
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let D : Finset ℕ := (Finset.range C.gates.length).filter fun i =>
    (gateAt C i).op = GateOp.or ∧ OrToOutput n C i
  let X : Finset ℕ := F ∪ D
  have hFD : Disjoint F D := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxF hxD
    have hxFand : (gateAt C x).op = GateOp.and := (hF x hxF).2.1
    have hxDor : (gateAt C x).op = GateOp.or := (Finset.mem_filter.mp hxD).2.1
    rw [hxFand] at hxDor
    cases hxDor
  have hXcard : X.card = F.card + D.card := by
    dsimp [X]
    rw [Finset.card_union_of_disjoint hFD]
  let S : Finset ℕ := X.filter fun x => n + x ≠ C.output
  have hex : ∀ x ∈ S, ∃ hp : ℕ × Fin 2,
      hp.1 ∈ D ∧ (gateAt C hp.1).inputs.getD hp.2.1 0 = n + x := by
    intro x hxS
    have hxS' := Finset.mem_filter.mp hxS
    have hxX := hxS'.1
    have hne := hxS'.2
    have hOrx : OrToOutput n C x := by
      rcases Finset.mem_union.mp hxX with hxF | hxD
      · exact (hF x hxF).2.2
      · exact (Finset.mem_filter.mp hxD).2.2
    have hb := output_bounds n C x hOrx
    have hklt : C.output - n < C.gates.length := by omega
    have heqout : n + (C.output - n) = C.output := by omega
    change OrReaches n C C.output x at hOrx
    rw [← heqout] at hOrx
    rw [orReaches_iff] at hOrx
    obtain ⟨_, hcase | ⟨hop, v, hv, hvl0, hvx⟩⟩ := hOrx
    · exfalso
      apply hne
      omega
    · have hvl : v < n + C.gates.length := by omega
      by_cases hv_eq : v = n + x
      · obtain ⟨p, hp⟩ := mem_inputs_pos n C hAO (C.output - n) (n + x) hklt (by simpa [hv_eq] using hv)
        refine ⟨(C.output - n, p), ?_, hp⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklt, ⟨hop, ?_⟩⟩
        change OrReaches n C C.output (C.output - n)
        rw [← heqout, orReaches_iff]
        constructor <;> omega
      · obtain ⟨h, hhlt, hop_h, hin_h, hor_h⟩ := exists_reader n C x v hvx.1 hvl hvx hv_eq
        obtain ⟨p, hp⟩ := mem_inputs_pos n C hAO h (n + x) hhlt hin_h
        refine ⟨(h, p), ?_, hp⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hhlt, ⟨hop_h, ?_⟩⟩
        change OrReaches n C C.output h
        rw [← heqout, orReaches_iff]
        refine ⟨by omega, Or.inr ?_⟩
        exact ⟨hop, v, hv, hvl0, hor_h⟩
  let gmap : ℕ → ℕ × Fin 2 := fun x =>
    if hx : x ∈ S then Classical.choose (hex x hx) else (0, 0)
  have gmap_spec : ∀ x (hx : x ∈ S),
      (gmap x).1 ∈ D ∧ (gateAt C (gmap x).1).inputs.getD (gmap x).2.1 0 = n + x := by
    intro x hx
    dsimp [gmap]
    rw [dif_pos hx]
    exact Classical.choose_spec (hex x hx)
  have hgmap_inj : Set.InjOn gmap (↑S : Set ℕ) := by
    intro a ha b hb hab
    have hpa := (gmap_spec a ha).2
    have hpb := (gmap_spec b hb).2
    have hsecond : (gmap a).2 = (gmap b).2 := congrArg Prod.snd hab
    have hfirst : (gmap a).1 = (gmap b).1 := congrArg Prod.fst hab
    rw [hfirst, hsecond] at hpa
    omega
  have hScard : S.card ≤ D.card * 2 := by
    have hle : S.card ≤ (D ×ˢ (Finset.univ : Finset (Fin 2))).card :=
      Finset.card_le_card_of_injOn gmap (by
        intro a ha
        exact Finset.mem_product.mpr ⟨(gmap_spec a ha).1, Finset.mem_univ _⟩)
        hgmap_inj
    rw [Finset.card_product] at hle
    simpa using hle
  let R : Finset ℕ := X.filter fun x => n + x = C.output
  have hsplit : X = S ∪ R := by
    ext x
    dsimp [S, R]
    by_cases hx : x ∈ X
    · by_cases hn : n + x = C.output
      · simp [hx, hn]
      · simp [hx, hn]
    · simp [hx]
  have hSRdisj : Disjoint S R := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxS hxR
    have hxS' := Finset.mem_filter.mp hxS
    have hxR' := Finset.mem_filter.mp hxR
    exact hxS'.2 hxR'.2
  have hXsplit : X.card = S.card + R.card := by
    rw [hsplit, Finset.card_union_of_disjoint hSRdisj]
  have hRcard : R.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    omega
  have hDset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (↑D : Set ℕ) := by
    ext i
    constructor
    · intro h
      change i ∈ D
      dsimp [D]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1,
        ⟨h.2.1, by simpa [OrToOutput] using h.2.2⟩⟩
    · intro h
      change i ∈ D at h
      dsimp [D] at h
      have h' := Finset.mem_filter.mp h
      exact ⟨Finset.mem_range.mp h'.1, h'.2.1, by simpa [OrToOutput] using h'.2.2⟩
  rw [hDset]
  simp
  have hmain : F.card + D.card ≤ D.card * 2 + 1 := by
    calc
      F.card + D.card = X.card := hXcard.symm
      _ = S.card + R.card := hXsplit
      _ ≤ D.card * 2 + 1 := by omega
  omega
