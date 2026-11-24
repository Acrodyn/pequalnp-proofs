import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3297

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false


lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k


open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

open PEqualNP.EdgeOwnership in
lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

open PEqualNP.EdgeOwnership in
lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩


def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs

def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)

lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega

lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]

lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i hc
    rw [inCone_iff n C i k hk] at hc
    obtain ⟨w, _, hn, hlt, h | h⟩ := hc
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

open PEqualNP.CleanedNonEdge in
lemma cnFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma cnStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
      true_and]
    constructor
    · rintro (h | ⟨w, ⟨hw, hn, hlt⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, hw, hn, hlt, h⟩
    · rintro (h | ⟨w, hw, hn, hlt, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, h⟩
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.not_mem_nil, or_false, false_and]

open PEqualNP.CleanedNonEdge in
lemma cnStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma cnFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact cnStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    g ∈ (orSets n C).getD k [] ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ g ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [cnFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, cnFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, cnFold_getD_lt n post _ m (by omega)]
    exact cnStep_getD_lt n _ gk m (by omega)
  have h3 := cnStep_mem_last n (pre.foldl (orStep n) []) gk g
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact h⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact h⟩

open PEqualNP.CleanedNonEdge in
lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [cnFold_length]
  simp

open PEqualNP.CleanedNonEdge in
lemma reaches_to (n : ℕ) (C : Circuit) :
    ∀ k g, g ∈ (orSets n C).getD k [] → g < C.gates.length ∧ OrR n C (n + k) (n + g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    have hk : k < C.gates.length := by
      by_contra hk
      have hnone : (orSets n C)[k]? = none :=
        List.getElem?_eq_none (by rw [orSets_len]; omega)
      rw [List.getD_eq_getElem?_getD, hnone] at hg
      simp at hg
    rw [orSets_iff n C g k hk] at hg
    rcases hg with rfl | ⟨hop, w, hw, hn, hlt, h⟩
    · exact ⟨hk, Relation.ReflTransGen.refl⟩
    · obtain ⟨h4, h5⟩ := ih (w - n) (by omega) g h
      have hw' : n + (w - n) = w := by omega
      rw [hw'] at h5
      exact ⟨h4, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hw⟩ h5⟩

open PEqualNP.CleanedNonEdge in
lemma orReaches_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w g : ℕ) :
    OrReaches n C w g ↔ (n ≤ w ∧ g < C.gates.length ∧ OrR n C w (n + g)) := by
  constructor
  · rintro ⟨hn, h⟩
    obtain ⟨h1, h2⟩ := reaches_to n C (w - n) g h
    have hw' : n + (w - n) = w := by omega
    rw [hw'] at h2
    exact ⟨hn, h1, h2⟩
  · rintro ⟨hn, hg, h⟩
    refine ⟨hn, ?_⟩
    clear hn
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have he : n + g - n = g := by omega
      rw [he, orSets_iff n C g g hg]
      exact Or.inl rfl
    | head h1 h2 ih =>
      rename_i u c
      have hle := orR_le n C hA _ _ h2
      have hlt := orStep_lt n C hA _ _ h1
      obtain ⟨k, rfl, hk, hop, hin⟩ := h1
      have he : n + k - n = k := by omega
      rw [he, orSets_iff n C g k hk]
      exact Or.inr ⟨hop, c, hin, by omega, hlt, ih⟩

lemma ao_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h3 _ hmem)
  refine ⟨h1 _ hmem, a, b, hab, ?_, ?_⟩
  · exact h2 k hk a (by rw [hab]; simp)
  · exact h2 k hk b (by rw [hab]; simp)

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.FactorSubst

lemma subst_len (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).gates.length = C.gates.length := by
  simp [substReads]

lemma subst_gateAt (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (k : ℕ) (hk : k < C.gates.length) :
    gateAt (substReads C n c sigma) k =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map fun i => if i = n + c then sigma k else i⟩ := by
  simp [gateAt, substReads, List.getD_eq_getElem?_getD, hk]

def InO (n : ℕ) (C : Circuit) (c k : ℕ) : Prop :=
  k < C.gates.length ∧ k ≠ c ∧ OrR n C (n + k) (n + c)

lemma inO_gt (n : ℕ) (C : Circuit) (hA : AO n C) (c k : ℕ) (h : InO n C c k) : c < k := by
  obtain ⟨_, hne, hR⟩ := h
  have := orR_le n C hA _ _ hR
  omega

lemma inO_or (n : ℕ) (C : Circuit) (c k : ℕ) (h : InO n C c k) :
    (gateAt C k).op = GateOp.or := by
  obtain ⟨_, hne, hR⟩ := h
  rcases Relation.ReflTransGen.cases_head hR with e | ⟨v, ⟨k', hk', _, hop, _⟩, _⟩
  · omega
  · have : k' = k := by omega
    rw [← this]; exact hop

lemma inO_of_or (n : ℕ) (C : Circuit) (c k t w : ℕ) (hk : k < C.gates.length)
    (hopc : (gateAt C c).op = GateOp.and)
    (hop : (gateAt C k).op = GateOp.or) (ht : t ∈ (gateAt C k).inputs) (htw : t = n + w)
    (hw : w = c ∨ InO n C c w) : InO n C c k := by
  refine ⟨hk, ?_, ?_⟩
  · intro e
    rw [e, hopc] at hop
    cases hop
  · refine Relation.ReflTransGen.head ⟨k, rfl, hk, hop, ht⟩ ?_
    rw [htw]
    rcases hw with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact h.2.2

lemma exists_reader (n : ℕ) (C : Circuit) (c w : ℕ) (h : InO n C c w) :
    ∃ r, r < C.gates.length ∧ n + c ∈ (gateAt C r).inputs ∧ OrR n C (n + w) (n + r) := by
  obtain ⟨_, hne, hR⟩ := h
  rcases Relation.ReflTransGen.cases_tail hR with e | ⟨v, hR', ⟨r, hv, hr, _, hmem⟩⟩
  · omega
  · exact ⟨r, hr, hmem, hv ▸ hR'⟩

theorem vals (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ) (hA : AO n C)
    (hc : c < C.gates.length) (hop : (gateAt C c).op = GateOp.and)
    (hin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r, r < C.gates.length → n + c ∈ (gateAt C r).inputs → sigma r = a ∨ sigma r = b)
    (hfr : ∀ g, g < C.gates.length → g ≠ c → ¬ InO n C c g → (gateAt C g).op = GateOp.and →
      ∀ u y w, ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
        (w = c ∨ InO n C c w) → u = n + w →
        (∀ w', (w' = c ∨ InO n C c w') → y ≠ n + w') ∧
        ∀ r, r < C.gates.length → n + c ∈ (gateAt C r).inputs → (r = g ∨ OrR n C u (n + r)) →
          (sigma r = b → ∀ z : Fin n → Bool, W n C z y = true → W n C z a = true) ∧
          (sigma r = a → ∀ z : Fin n → Bool, W n C z y = true → W n C z b = true))
    (hag : ∀ g, g < C.gates.length → g ≠ c → ¬ InO n C c g → ∀ u w, u ∈ (gateAt C g).inputs →
        (w = c ∨ InO n C c w) → u = n + w →
        ∀ r1 r2, r1 < C.gates.length → r2 < C.gates.length →
          n + c ∈ (gateAt C r1).inputs → n + c ∈ (gateAt C r2).inputs →
          OrR n C u (n + r1) → OrR n C u (n + r2) → sigma r1 = sigma r2)
    (x : Fin n → Bool) :
    ∀ k, k < C.gates.length →
      (¬ InO n C c k → k ≠ c →
        W n (substReads C n c sigma) x (n + k) = W n C x (n + k)) ∧
      (InO n C c k →
        (W n C x (n + k) = true → W n (substReads C n c sigma) x (n + k) = true) ∧
        ∀ s, (s = a ∨ s = b) →
          (∀ r, r < C.gates.length → n + c ∈ (gateAt C r).inputs →
            OrR n C (n + k) (n + r) → sigma r = s) →
          W n (substReads C n c sigma) x (n + k) = true →
            (W n C x (n + k) = true ∨ W n C x s = true)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  have hk' : k < (substReads C n c sigma).gates.length := by rw [subst_len]; exact hk
  obtain ⟨hac, hbc⟩ : a < n + c ∧ b < n + c := by
    obtain ⟨_, a', b', hin', ha', hb'⟩ := hA c hc
    rw [hin] at hin'
    simp only [List.cons.injEq, and_true] at hin'
    obtain ⟨rfl, rfl⟩ := hin'
    exact ⟨ha', hb'⟩
  have hWc : W n C x (n + c) = (W n C x a && W n C x b) :=
    W_and n C x c hc hop a b hin hac hbc
  have weq : ∀ p, p < n + k → p ≠ n + c → (∀ j, p = n + j → ¬ InO n C c j) →
      W n (substReads C n c sigma) x p = W n C x p := by
    intro p hp hpc hno
    by_cases hpn : p < n
    · rw [W_input n _ x p hpn, W_input n C x p hpn]
    · obtain ⟨j, rfl⟩ : ∃ j, p = n + j := ⟨p - n, by omega⟩
      exact (ih j (by omega) (by omega)).1 (hno j rfl) (by omega)
  have wsig : ∀ s, (s = a ∨ s = b) → n + c < n + k →
      W n (substReads C n c sigma) x s = W n C x s := by
    intro s hs hck
    apply weq s (by rcases hs with rfl | rfl <;> omega)
      (by rcases hs with rfl | rfl <;> omega)
    intro j hj hO
    have := inO_gt n C hA c j hO
    rcases hs with rfl | rfl <;> omega
  obtain ⟨hopk, p, q, hink, hp, hq⟩ := hA k hk
  have hmp : p ∈ (gateAt C k).inputs := by rw [hink]; simp
  have hmq : q ∈ (gateAt C k).inputs := by rw [hink]; simp
  have hsub : ∀ t, t ∈ (gateAt C k).inputs → t < n + k →
      (if t = n + c then sigma k else t) < n + k := by
    intro t ht htk
    split_ifs with h
    · rcases hsig k hk (h ▸ ht) with e | e <;> omega
    · exact htk
  have hgk' : (gateAt (substReads C n c sigma) k).inputs =
      [if p = n + c then sigma k else p, if q = n + c then sigma k else q] := by
    rw [subst_gateAt C n c sigma k hk, hink]; rfl
  have hopk' : (gateAt (substReads C n c sigma) k).op = (gateAt C k).op := by
    rw [subst_gateAt C n c sigma k hk]
  have low : ∀ t, t ∈ (gateAt C k).inputs → t < n + k → W n C x t = true →
      W n (substReads C n c sigma) x (if t = n + c then sigma k else t) = true := by
    intro t ht htk hv
    by_cases h : t = n + c
    · rw [if_pos h]
      have hs := hsig k hk (h ▸ ht)
      rw [wsig _ hs (h ▸ htk)]
      rw [h, hWc] at hv
      simp only [Bool.and_eq_true] at hv
      rcases hs with e | e <;> rw [e]
      · exact hv.1
      · exact hv.2
    · rw [if_neg h]
      by_cases hO : ∃ j, t = n + j ∧ InO n C c j
      · obtain ⟨j, rfl, hj⟩ := hO
        exact ((ih j (by omega) hj.1).2 hj).1 hv
      · rw [weq t htk h (fun j e hj => hO ⟨j, e, hj⟩)]
        exact hv
  have up : ∀ s, (s = a ∨ s = b) →
      (∀ r, r < C.gates.length → n + c ∈ (gateAt C r).inputs →
        OrR n C (n + k) (n + r) → sigma r = s) →
      (gateAt C k).op = GateOp.or →
      ∀ t, t ∈ (gateAt C k).inputs → t < n + k →
      W n (substReads C n c sigma) x (if t = n + c then sigma k else t) = true →
        (W n C x t = true ∨ W n C x s = true) := by
    intro s hs Hs hor t ht htk hv
    by_cases h : t = n + c
    · rw [if_pos h] at hv
      have e : sigma k = s := Hs k hk (h ▸ ht) Relation.ReflTransGen.refl
      rw [e, wsig s hs (h ▸ htk)] at hv
      exact Or.inr hv
    · rw [if_neg h] at hv
      by_cases hO : ∃ j, t = n + j ∧ InO n C c j
      · obtain ⟨j, rfl, hj⟩ := hO
        exact ((ih j (by omega) hj.1).2 hj).2 s hs
          (fun r hr hmem hR => Hs r hr hmem
            (Relation.ReflTransGen.head ⟨k, rfl, hk, hor, ht⟩ hR)) hv
      · rw [weq t htk h (fun j e hj => hO ⟨j, e, hj⟩)] at hv
        exact Or.inl hv
  have fr : (gateAt C k).op = GateOp.and → k ≠ c → ¬ InO n C c k →
      ∀ u y w, ((gateAt C k).inputs = [u, y] ∨ (gateAt C k).inputs = [y, u]) →
      u < n + k → y < n + k → u = n + w → (w = c ∨ InO n C c w) →
      (W n (substReads C n c sigma) x (if u = n + c then sigma k else u) &&
        W n (substReads C n c sigma) x (if y = n + c then sigma k else y)) =
      (W n C x u && W n C x y) := by
    intro hand hkc hnO u y w hio huk hyk hu hw
    have hmu : u ∈ (gateAt C k).inputs := by rcases hio with e | e <;> rw [e] <;> simp
    obtain ⟨hy, hrd⟩ := hfr k hk hkc hnO hand u y w hio hw hu
    have hyc : y ≠ n + c := hy c (Or.inl rfl)
    have ey : W n (substReads C n c sigma) x y = W n C x y :=
      weq y hyk hyc (fun j e hj => hy j (Or.inr hj) e)
    rw [if_neg hyc, ey]
    rcases hw with rfl | hw
    · rw [if_pos hu]
      have hmem : n + w ∈ (gateAt C k).inputs := hu ▸ hmu
      have hs := hsig k hk hmem
      have h1 := hrd k hk hmem (Or.inl rfl)
      rw [wsig _ hs (hu ▸ huk), hu, hWc]
      have h1a := fun e => (h1.1 e) x
      have h1b := fun e => (h1.2 e) x
      rcases hs with e | e
      · have h2 := h1b e
        rw [e]
        revert h2
        cases W n C x a <;> cases W n C x b <;> cases W n C x y <;> simp
      · have h2 := h1a e
        rw [e]
        revert h2
        cases W n C x a <;> cases W n C x b <;> cases W n C x y <;> simp
    · have hwc : u ≠ n + c := by
        have := hw.2.1
        omega
      rw [if_neg hwc]
      obtain ⟨r, hr, hmem, hR⟩ := exists_reader n C c w hw
      have hs := hsig r hr hmem
      have hwk : w < k := by omega
      have hB := (ih w hwk hw.1).2 hw
      have hlow := hB.1
      have hup := hB.2 (sigma r) hs (fun r2 hr2 hmem2 hR2 =>
        hag k hk hkc hnO u w hmu (Or.inr hw) hu r2 r hr2 hr hmem2 hmem (hu ▸ hR2) (hu ▸ hR))
      have h1 := hrd r hr hmem (Or.inr (hu ▸ hR))
      have h1a := fun e => (h1.1 e) x
      have h1b := fun e => (h1.2 e) x
      have hcu : W n C x (n + c) = true → W n C x (n + w) = true :=
        orR_mono n C hA x _ _ hw.2.2
      rw [hWc] at hcu
      rw [hu]
      rcases hs with e | e
      · have h2 := h1b e
        rw [e] at hup
        revert h2 hup hlow hcu
        cases W n C x a <;> cases W n C x b <;> cases W n C x y <;>
          cases W n C x (n + w) <;>
          cases W n (substReads C n c sigma) x (n + w) <;> simp
      · have h2 := h1a e
        rw [e] at hup
        revert h2 hup hlow hcu
        cases W n C x a <;> cases W n C x b <;> cases W n C x y <;>
          cases W n C x (n + w) <;>
          cases W n (substReads C n c sigma) x (n + w) <;> simp
  constructor
  · intro hnO hkc
    by_cases hex : ∃ t ∈ (gateAt C k).inputs, ∃ w, t = n + w ∧ (w = c ∨ InO n C c w)
    · obtain ⟨t, ht, w, htw, hw⟩ := hex
      have hand : (gateAt C k).op = GateOp.and := by
        rcases hopk with h | h
        · exact h
        · exact absurd (inO_of_or n C c k t w hk hop h ht htw hw) hnO
      rw [W_and n _ x k hk' (hopk'.trans hand) _ _ hgk' (hsub p hmp hp) (hsub q hmq hq),
        W_and n C x k hk hand p q hink hp hq]
      rw [hink] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact fr hand hkc hnO t q w (Or.inl hink) hp hq htw hw
      · rw [Bool.and_comm, fr hand hkc hnO t p w (Or.inr hink) hq hp htw hw, Bool.and_comm]
    · have ep : W n (substReads C n c sigma) x (if p = n + c then sigma k else p) = W n C x p := by
        have hpc : p ≠ n + c := fun e => hex ⟨p, hmp, c, e, Or.inl rfl⟩
        rw [if_neg hpc]
        exact weq p hp hpc (fun j e hj => hex ⟨p, hmp, j, e, Or.inr hj⟩)
      have eq : W n (substReads C n c sigma) x (if q = n + c then sigma k else q) = W n C x q := by
        have hqc : q ≠ n + c := fun e => hex ⟨q, hmq, c, e, Or.inl rfl⟩
        rw [if_neg hqc]
        exact weq q hq hqc (fun j e hj => hex ⟨q, hmq, j, e, Or.inr hj⟩)
      rcases hopk with hand | hor
      · rw [W_and n _ x k hk' (hopk'.trans hand) _ _ hgk' (hsub p hmp hp) (hsub q hmq hq),
          W_and n C x k hk hand p q hink hp hq, ep, eq]
      · rw [W_or n _ x k hk' (hopk'.trans hor) _ _ hgk' (hsub p hmp hp) (hsub q hmq hq),
          W_or n C x k hk hor p q hink hp hq, ep, eq]
  · intro hO
    have hor := inO_or n C c k hO
    rw [W_or n _ x k hk' (hopk'.trans hor) _ _ hgk' (hsub p hmp hp) (hsub q hmq hq),
      W_or n C x k hk hor p q hink hp hq]
    constructor
    · intro hv
      simp only [Bool.or_eq_true] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl (low p hmp hp hv)
      · exact Or.inr (low q hmq hq hv)
    · intro s hs Hs hv
      simp only [Bool.or_eq_true] at hv ⊢
      rcases hv with hv | hv
      · rcases up s hs Hs hor p hmp hp hv with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases up s hs Hs hor q hmq hq hv with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

lemma subst_out (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).output = C.output := rfl

lemma mem_orc (n : ℕ) (C : Circuit) (hA : AO n C) (c : ℕ) (hc : c < C.gates.length) (w : ℕ) :
    w ∈ orClosure n C c ↔ InO n C c w := by
  simp only [PEqualNP.FactorSubst.orClosure, Finset.mem_filter, Finset.mem_range, InO, orReaches_iff n C hA]
  constructor
  · rintro ⟨h1, h2, _, _, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by omega, hc, h3⟩

lemma mem_ins (n : ℕ) (C : Circuit) (hA : AO n C) (c : ℕ) (hc : c < C.gates.length) (w : ℕ) :
    w ∈ insert c (orClosure n C c) ↔ (w = c ∨ InO n C c w) := by
  rw [Finset.mem_insert, mem_orc n C hA c hc]

lemma mem_readers (n : ℕ) (C : Circuit) (c r : ℕ) :
    r ∈ PEqualNP.TopForm.readers n C c ↔ r < C.gates.length ∧ n + c ∈ (gateAt C r).inputs := by
  simp [PEqualNP.TopForm.readers]

lemma mem_frontier (n : ℕ) (C : Circuit) (hA : AO n C) (c : ℕ) (hc : c < C.gates.length)
    (g : ℕ) :
    g ∈ frontier n C c ↔ g < C.gates.length ∧ g ≠ c ∧ ¬ InO n C c g ∧
      ∃ w, (w = c ∨ InO n C c w) ∧ n + w ∈ (gateAt C g).inputs := by
  simp only [PEqualNP.FactorSubst.frontier, Finset.mem_filter, Finset.mem_range]
  rw [mem_orc n C hA c hc]
  constructor
  · rintro ⟨h1, h2, h3, w, hw, hm⟩
    exact ⟨h1, h2, h3, w, (mem_ins n C hA c hc w).1 hw, hm⟩
  · rintro ⟨h1, h2, h3, w, hw, hm⟩
    exact ⟨h1, h2, h3, w, (mem_ins n C hA c hc w).2 hw, hm⟩

lemma cone_sub (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ) (hA : AO n C)
    (hc : c < C.gates.length) (hin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r, r < C.gates.length → n + c ∈ (gateAt C r).inputs → sigma r = a ∨ sigma r = b) :
    ∀ m, m < C.gates.length → ∀ j, InCone n (substReads C n c sigma) j m →
      InCone n C j m ∧ j ≠ c := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm j h
  obtain ⟨hac, hbc⟩ : a < n + c ∧ b < n + c := by
    obtain ⟨_, a', b', hin', ha', hb'⟩ := hA c hc
    rw [hin] at hin'
    simp only [List.cons.injEq, and_true] at hin'
    obtain ⟨rfl, rfl⟩ := hin'
    exact ⟨ha', hb'⟩
  have hlen : ∀ i, i ∈ (gateAt C m).inputs → i < n + m := by
    intro i hi
    obtain ⟨_, p, q, hpq, hp, hq⟩ := hA m hm
    rw [hpq] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  rw [inCone_iff n _ j m (by rw [subst_len]; exact hm), subst_gateAt C n c sigma m hm] at h
  obtain ⟨w, hw, hnw, hwm, hj⟩ := h
  simp only [List.mem_map] at hw
  obtain ⟨i, hi, rfl⟩ := hw
  have him := hlen i hi
  by_cases h : i = n + c
  · have e : (if i = n + c then sigma m else i) = sigma m := by simp [h]
    rw [e] at hnw hwm hj
    have hs := hsig m hm (h ▸ hi)
    have hmemc : n + (sigma m - n) ∈ (gateAt C c).inputs := by
      have e2 : n + (sigma m - n) = sigma m := by omega
      rw [e2, hin]
      rcases hs with e3 | e3 <;> simp [e3]
    have hlt : sigma m < n + c := by rcases hs with e3 | e3 <;> omega
    have key : InCone n C j c ∧ j ≠ c := by
      rcases hj with rfl | hj
      · exact ⟨inCone_c1 n C hA (sigma m - n) c hc hmemc, by omega⟩
      · obtain ⟨h1, _⟩ := ih (sigma m - n) (by omega) (by omega) j hj
        have h3 := inCone_lt n C (sigma m - n) (by omega) j h1
        exact ⟨inCone_c2 n C hA j (sigma m - n) c hc h1 hmemc, by omega⟩
    exact ⟨inCone_c2 n C hA j c m hm key.1 (h ▸ hi), key.2⟩
  · have e : (if i = n + c then sigma m else i) = i := by simp [h]
    rw [e] at hnw hwm hj
    have hmem : n + (i - n) ∈ (gateAt C m).inputs := by
      have e2 : n + (i - n) = i := by omega
      rw [e2]; exact hi
    rcases hj with rfl | hj
    · exact ⟨inCone_c1 n C hA (i - n) m hm hmem, by omega⟩
    · obtain ⟨h1, h2⟩ := ih (i - n) (by omega) (by omega) j hj
      exact ⟨inCone_c2 n C hA j (i - n) m hm h1 hmem, h2⟩

lemma inCone_len (n : ℕ) (C : Circuit) (j m : ℕ) (h : InCone n C j m) : m < C.gates.length := by
  by_contra hm
  have hl : (cones n C).length = C.gates.length := by
    simp only [cones]
    rw [coneFold_length]
    simp
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

lemma live_sub (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ) (hA : AO n C)
    (hc : c < C.gates.length) (hin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r, r < C.gates.length → n + c ∈ (gateAt C r).inputs → sigma r = a ∨ sigma r = b)
    (hout : C.output ≠ n + c) :
    liveGates n (substReads C n c sigma) ⊆ (liveGates n C).erase c := by
  intro j hj
  simp only [PEqualNP.FactorSubst.liveGates, Finset.mem_filter, Finset.mem_range, Finset.mem_erase] at hj ⊢
  rw [subst_len, subst_out] at hj
  obtain ⟨hjl, hn, h⟩ := hj
  rcases h with rfl | h
  · exact ⟨by omega, hjl, hn, Or.inl rfl⟩
  · have hm : C.output - n < C.gates.length := by
      have := inCone_len n _ j _ h
      rw [subst_len] at this
      exact this
    obtain ⟨h1, h2⟩ := cone_sub n C c a b sigma hA hc hin hsig _ hm j h
    exact ⟨h2, hjl, hn, Or.inr h1⟩

theorem main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  intro n C c a b sigma hAO hc hop hin hsig hfr hag hout hlive
  have hA := ao_of n C hAO
  have hsig' : ∀ r, r < C.gates.length → n + c ∈ (gateAt C r).inputs →
      sigma r = a ∨ sigma r = b :=
    fun r hr hm => hsig r ((mem_readers n C c r).2 ⟨hr, hm⟩)
  refine ⟨?_, ?_⟩
  · intro k hk hkc hkO z
    have hv := (vals n C c a b sigma hA hc hop hin hsig' ?_ ?_ z k hk).1
      (fun h => hkO ((mem_orc n C hA c hc k).2 h)) hkc
    · exact hv
    · intro g hg hgc hgO hand u y w hio hw hu
      have hmu : u ∈ (gateAt C g).inputs := by rcases hio with e | e <;> rw [e] <;> simp
      have hgf : g ∈ frontier n C c :=
        (mem_frontier n C hA c hc g).2 ⟨hg, hgc, hgO, w, hw, hu ▸ hmu⟩
      obtain ⟨h1, h2⟩ := hfr g hgf hand u y hio ⟨w, (mem_ins n C hA c hc w).2 hw, hu⟩
      refine ⟨fun w' hw' => h1 w' ((mem_ins n C hA c hc w').2 hw'), ?_⟩
      intro r hr hmem hor
      exact h2 r ((mem_readers n C c r).2 ⟨hr, hmem⟩)
        (hor.imp id (fun hR => (orReaches_iff n C hA u r).2 ⟨by omega, hr, hR⟩))
    · intro g hg hgc hgO u w hu hw huw r1 r2 hr1 hr2 hm1 hm2 hR1 hR2
      have hgf : g ∈ frontier n C c :=
        (mem_frontier n C hA c hc g).2 ⟨hg, hgc, hgO, w, hw, huw ▸ hu⟩
      exact hag g hgf u hu r1 ((mem_readers n C c r1).2 ⟨hr1, hm1⟩)
        r2 ((mem_readers n C c r2).2 ⟨hr2, hm2⟩)
        ((orReaches_iff n C hA u r1).2 ⟨by omega, hr1, hR1⟩)
        ((orReaches_iff n C hA u r2).2 ⟨by omega, hr2, hR2⟩)
  · have hs := Finset.card_le_card (live_sub n C c a b sigma hA hc hin hsig'
      (hout c (Finset.mem_insert_self _ _)))
    rw [Finset.card_erase_of_mem hlive] at hs
    have hp := Finset.card_pos.mpr ⟨c, hlive⟩
    unfold PEqualNP.FactorSubst.liveSize
    omega

end PEqualNP.Outside.L_meta_3297

theorem PEqualNP.Outside.L_meta_3297 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  exact PEqualNP.Outside.L_meta_3297.main
