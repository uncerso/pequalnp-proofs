import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

-- The permutations and their circuit transport adapt arguiot's PR 4706.
-- The boundary test columns and wire simulation adapt KainanP's PR 7600.
-- Rows 0 through 20 are incident pairs and rows 21 through 57 are maximal independent sets.
-- Rows 58 and 59 are the two singletons and rows 60 and 61 are the directional responses.
-- A nonincident first AND can be clamped to zero. This preserves positive rows
-- and can only decrease the other rows under every subsequent operation.
-- For an incident first AND there are four representative first columns.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2346_71
  (withoutEdge : let raw := ([2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List ℕ).map fun v => fun t : Fin 62 => v.testBit t.val
    let seed := raw ++ [(fun _ : Fin 62 => false)]
    ¬ ∃ s : List (Fin 62 → Bool), s.length ≤ 26 ∧ (fun t => decide (t.val < 21)) ∈ s ∧
      ∀ j < s.length, ∃ a b : ℕ, a ≠ b ∧ a < 15+j ∧ b < 15+j ∧
        let A := (seed++s).getD a (fun _ => false)
        let B := (seed++s).getD b (fun _ => false)
        s.getD j (fun _ => false) = (fun t => A t || B t) ∨
          s.getD j (fun _ => false) = (fun t : Fin 62 => if t=60 then ((A 58 && B 60) || (A 60 && B 58)) else if t=61 then ((A 59 && B 61) || (A 61 && B 59)) else (A t && B t)))
  (withEdge : let raw := ([2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List ℕ).map fun v => fun t : Fin 62 => v.testBit t.val
    ∀ m ∈ ([3458764513820540929, 2, 16, 64] : List ℕ),
    let seed := raw ++ [(fun t : Fin 62 => m.testBit t.val)]
    ¬ ∃ s : List (Fin 62 → Bool), s.length ≤ 26 ∧ (fun t => decide (t.val < 21)) ∈ s ∧
      ∀ j < s.length, ∃ a b : ℕ, a ≠ b ∧ a < 15+j ∧ b < 15+j ∧
        let A := (seed++s).getD a (fun _ => false)
        let B := (seed++s).getD b (fun _ => false)
        s.getD j (fun _ => false) = (fun t => A t || B t) ∨
          s.getD j (fun _ => false) = (fun t : Fin 62 => if t=60 then ((A 58 && B 60) || (A 60 && B 58)) else if t=61 then ((A 59 && B 61) || (A 61 && B 59)) else (A t && B t)))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  have canonical : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (gateAt C 0).op = .and →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      (let a := opnd C 0 0
       let b := opnd C 0 1
       Nat.testBit 365118556550 (14 * min a b + max a b) = true) →
      (∀ s : Bool, ∃ v : ℕ → Bool,
        let W := C.wires (List.ofFn (fun i : Fin 14 =>
          decide (i = if s then 0 else 7)))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
        (∀ j < C.size,
          let g := gateAt C j
          let a := opnd C j 0
          let b := opnd C j 1
          (g.op = .and →
            v (14 + j) = ((W.getD a false && v b) || (v a && W.getD b false))) ∧
          (g.op = .or → v (14 + j) = (v a || v b))) ∧ v C.output = false) →
      False := by
    intro C cap ao distinct first computes orbit traces
    let wstep : List Bool → Gate → List Bool :=
      fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    have wfold_len : ∀ (gs : List Gate) (xs : List Bool),
        (gs.foldl wstep xs).length = xs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro xs; simp
      | cons g rest ih =>
        intro xs
        simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
        omega
    have wfold_getD_lt : ∀ (gs : List Gate) (xs : List Bool) (r : ℕ),
        r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
      intro gs
      induction gs with
      | nil => intro xs r _; rfl
      | cons g rest ih =>
        intro xs r hr
        simp only [List.foldl_cons]
        have hr' : r < (wstep xs g).length := by
          simp only [wstep, List.length_append, List.length_singleton]; omega
        rw [ih (wstep xs g) r hr']
        simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
    have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
    have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
    have wireVal_input : ∀ (D : Circuit) (x : Fin 14 → Bool) (r : ℕ) (hr : r < 14),
        wireVal 14 D r x = x ⟨r, hr⟩ := by
      intro D x r hr
      have hlen : (List.ofFn x).length = 14 := List.length_ofFn
      have hlt : r < (List.ofFn x).length := by omega
      change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
      rw [wfold_getD_lt D.gates (List.ofFn x) r hlt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hr]
    have wireVal_gate : ∀ (D : Circuit) (x : Fin 14 → Bool) (k : ℕ) (g : Gate),
        D.gates[k]? = some g → (∀ i ∈ g.inputs, i < 14 + k) →
        wireVal 14 D (14 + k) x = g.op.eval (g.inputs.map fun i => wireVal 14 D i x) := by
      intro D x k g hgk hlt
      have hk : k < D.gates.length := by
        by_contra h
        rw [List.getElem?_eq_none (by omega)] at hgk
        cases hgk
      have hg_eq : D.gates[k] = g := by
        rw [List.getElem?_eq_getElem hk] at hgk
        exact Option.some.inj hgk
      have hsplit : D.gates = D.gates.take k ++ g :: D.gates.drop (k + 1) := by
        rw [← hg_eq, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
      let pref := (D.gates.take k).foldl wstep (List.ofFn x)
      have hpref_len : pref.length = 14 + k := by
        dsimp only [pref]
        rw [wfold_len, List.length_ofFn, List.length_take]
        omega
      have hwires_eq : D.wires (List.ofFn x) =
          (D.gates.drop (k + 1)).foldl wstep (wstep pref g) := by
        change D.gates.foldl wstep (List.ofFn x) = _
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have hpref_get : ∀ i < 14 + k, pref.getD i false = wireVal 14 D i x := by
        intro i hi
        change pref.getD i false = (D.wires (List.ofFn x)).getD i false
        rw [hwires_eq]
        have hi1 : i < (wstep pref g).length := by
          simp only [wstep, List.length_append, List.length_singleton]; omega
        rw [wfold_getD_lt _ _ i hi1]
        have hi0 : i < pref.length := by omega
        simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0]
      change (D.wires (List.ofFn x)).getD (14 + k) false = _
      rw [hwires_eq]
      have hidx : 14 + k < (wstep pref g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [wfold_getD_lt _ _ (14 + k) hidx]
      have hstep_at : (wstep pref g).getD (14 + k) false =
          g.op.eval (g.inputs.map fun i => pref.getD i false) := by
        simp only [wstep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), hpref_len]
        simp
      rw [hstep_at]
      congr 1
      exact List.map_congr_left fun i hi => hpref_get i (hlt i hi)
    let base : List Nat := [2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916]
    let seed := base.map fun v => fun t : Fin 62 => v.testBit t.val
    let input (t : Fin 62) (i : Fin 14) := (base.getD i.val 0).testBit t.val
    let single (b : Bool) (i : Fin 14) := decide (i = if b=true then 0 else 7)
    have s58 (i : Fin 14) : input 58 i = single true i := by revert i; decide +kernel
    have s59 (i : Fin 14) : input 59 i = single false i := by revert i; decide +kernel
    have s60 (i : Fin 14) : input 60 i = decide (i.val=7) := by revert i; decide +kernel
    have s61 (i : Fin 14) : input 61 i = decide (i.val=0) := by revert i; decide +kernel
    have e58 : input 58=single true := funext s58
    have e59 : input 59=single false := funext s59
    choose D hd using traces
    let V (i : Nat) (t : Fin 62) : Bool := if t=60 then D true i else if t=61 then D false i else wireVal 14 C i (input t)
    let seq := List.ofFn (fun j : Fin C.size => V (14+j.val))
    have seqLen : seq.length=C.size := List.length_ofFn
    have seedLen : seed.length=14 := rfl
    have inputV (i : Fin 14) : V i.val = fun t => input t i := by
      funext t
      by_cases h : t=60
      · subst t; simp only [V,ite_true,s60]; simpa using (hd true).1 i.val i.isLt
      by_cases k : t=61
      · subst t; simp only [V,show (61:Fin 62)≠60 by decide,ite_false,ite_true,s61]; simpa using (hd false).1 i.val i.isLt
      · simp only [V,h,k,ite_false]; exact wireVal_input C _ _ i.isLt
    have publicWire (a : Nat) (ha : a<14+C.size) : (seed++seq).getD a (fun _ => false) = V a := by
      by_cases low : a<14
      · let i : Fin 14 := ⟨a,low⟩
        rw [List.getD_append _ _ _ _ (by omega)]
        change seed.getD i.val _ = V i.val
        rw [inputV]
        have hbase : i.val<base.length := i.isLt
        simp only [seed,List.getD_eq_getElem _ _ (show i.val<seed.length by omega), List.getElem_map]
        funext t; simp only [input,List.getD_eq_getElem _ _ hbase]
      · let j : Fin C.size := ⟨a-14,by omega⟩
        have eq : a=14+j.val := by dsimp [j];omega
        simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (show seed.length≤a by omega),seedLen,seq,List.getElem?_ofFn,dif_pos (show a-14<C.size by omega),Option.getD_some]
        congr 1; omega
    have outBound : C.output<14+C.size := by
      by_contra! beyond
      have pos := (computes (fun _ => true)).mpr ⟨0,0,Or.inl rfl,rfl,rfl⟩
      change (C.gates.foldl wstep (List.ofFn (fun _ : Fin 14 => true))).getD C.output false=true at pos
      rw [List.getD_eq_default _ _ (by rw [wfold_len,List.length_ofFn];exact beyond)] at pos
      exact Bool.noConfusion pos
    have outputGate : 14≤C.output := by
      by_contra! low
      let i : Fin 14 := ⟨C.output,low⟩
      let x (v : Fin 14) := decide (v=i)
      have lit : C.eval (List.ofFn x)=true := (wireVal_input C x _ low).trans (by simp [x,i])
      obtain ⟨p,l,_,hp,hl⟩ := (computes x).mp lit
      have bad := congrArg Fin.val ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
      change p.val=7+l.val at bad;omega
    have outValue : V C.output = fun t => decide (t.val<21) := by
      funext t
      by_cases h60 : t=60
      · subst t; change D true C.output=false; exact (hd true).2.2
      by_cases h61 : t=61
      · subst t; change D false C.output=false; exact (hd false).2.2
      have table : ∀ t : Fin 62, t.val < 58 →
          ((∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ input t (Fin.castAdd 7 p)=true ∧
              input t (Fin.natAdd 7 l)=true) ↔ t.val < 21) := by
        dsimp only [input,base]
        decide +kernel
      by_cases low : t.val < 58
      · simp only [V,h60,h61,ite_false]
        change C.eval (List.ofFn (input t)) = decide (t.val < 21)
        exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using (computes _).trans (table t low))
      · have options : t=58 ∨ t=59 := by
          have a : t.val≠60 := fun eq => h60 (Fin.ext eq)
          have b : t.val≠61 := fun eq => h61 (Fin.ext eq)
          have d : t.val=58 ∨ t.val=59 := by omega
          exact d.imp (fun v => Fin.ext v) (fun v => Fin.ext v)
        have quiet (b : Bool) : C.eval (List.ofFn (single b))=false := by
          cases eq : C.eval (List.ofFn (single b)) with
          | false => rfl
          | true =>
            obtain ⟨p,l,_,hp,hl⟩ := (computes _).mp eq
            have bad := congrArg Fin.val ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
            change p.val=7+l.val at bad;omega
        rcases options with rfl|rfl
        · change C.eval (List.ofFn (input 58))=false; rw [e58];exact quiet true
        · change C.eval (List.ofFn (input 59))=false; rw [e59];exact quiet false
    let add (A B : Fin 62 → Bool) := fun t => A t || B t
    let mul (A B : Fin 62 → Bool) := fun t : Fin 62 => if t=60 then ((A 58 && B 60) || (A 60 && B 58)) else if t=61 then ((A 59 && B 61) || (A 61 && B 59)) else (A t && B t)
    have rules (j : ℕ) (hj : j<C.size) :
        let a := opnd C j 0
        let b := opnd C j 1
        a ≠ b ∧ a < 14+j ∧ b < 14+j ∧
        ((gateAt C j).op = GateOp.and ∧ V (14+j) = mul (V a) (V b) ∨
         (gateAt C j).op = GateOp.or ∧ V (14+j) = add (V a) (V b)) := by
      have valid : j<C.gates.length := by change j<C.size; omega
      let g := gateAt C j
      have slot : C.gates[j]?=some g := List.getElem?_eq_some_iff.mpr ⟨valid,by change C.gates[j]=C.gates.getD j _; rw [List.getD_eq_getElem _ _ valid]⟩
      have ing := List.mem_of_getElem? slot
      let a := opnd C j 0
      let b := opnd C j 1
      have form : g.inputs=[a,b] := by
        have sz := ao.2.2 g ing
        rcases ins : g.inputs with _ | ⟨u, tail⟩
        · simp [ins] at sz
        · rcases rest : tail with _ | ⟨v,rest'⟩
          · simp [ins,rest] at sz
          · have z : rest'=[] := List.length_eq_zero_iff.mp (by simp only [ins,rest,List.length_cons] at sz; omega)
            change u::v::rest'=[g.inputs.getD 0 0,g.inputs.getD 1 0]; simp [ins,rest,z]
      have early := ao.2.1 j valid
      have ha := early a (by change a∈g.inputs;rw [form];simp)
      have hb := early b (by change b∈g.inputs;rw [form];simp)
      have wire (x : Fin 14→Bool) : wireVal 14 C (14+j) x = g.op.eval [wireVal 14 C a x,wireVal 14 C b x] := by
        rw [wireVal_gate C x j g slot early,form] <;> rfl
      refine ⟨distinct j valid,ha,hb,?_⟩
      rcases ao.1 g ing with andGate | orGate
      · left
        refine ⟨andGate,?_⟩; funext t
        by_cases h : t=60
        · subst t
          change D true (14+j) = ((wireVal 14 C a (input 58) && D true b) || (D true a && wireVal 14 C b (input 58)))
          rw [e58];exact ((hd true).2.1 j valid).1 andGate
        by_cases h' : t=61
        · subst t
          change D false (14+j) = ((wireVal 14 C a (input 59) && D false b) || (D false a && wireVal 14 C b (input 59)))
          rw [e59];exact ((hd false).2.1 j valid).1 andGate
        · simp only [mul,V,h,h',ite_false];exact (wire _).trans (andGate ▸ eval_and _ _)
      · right; refine ⟨orGate,?_⟩; funext t
        by_cases h : t=60
        · subst t; change D true (14+j) = (D true a || D true b);exact ((hd true).2.1 j valid).2 orGate
        by_cases h' : t=61
        · subst t; change D false (14+j) = (D false a || D false b);exact ((hd false).2.1 j valid).2 orGate
        · simp only [add,V,h,h',ite_false]; exact (wire _).trans (orGate ▸ eval_or _ _)
    let Keeps (U W : Fin 62 → Bool) : Prop :=
      (∀ t, U t = true → W t = true) ∧ ∀ t, t.val < 21 → U t = W t
    have same (W : Fin 62 → Bool) : Keeps W W := ⟨fun _ => id, fun _ _ => rfl⟩
    have andUp : ∀ a b c d : Bool, (a=true → c=true) → (b=true → d=true) →
        (a && b)=true → (c && d)=true := by decide
    have orUp : ∀ a b c d : Bool, (a=true → c=true) → (b=true → d=true) →
        (a || b)=true → (c || d)=true := by decide
    have combine (A B A' B' : Fin 62 → Bool) (ha : Keeps A' A) (hb : Keeps B' B) :
        Keeps (add A' B') (add A B) ∧ Keeps (mul A' B') (mul A B) := by
      refine ⟨⟨fun t => orUp _ _ _ _ (ha.1 t) (hb.1 t), ?_⟩, ⟨?_, ?_⟩⟩
      · intro t ht
        simp only [add, ha.2 t ht, hb.2 t ht]
      · intro t
        dsimp only [mul]
        split
        · exact orUp _ _ _ _ (andUp _ _ _ _ (ha.1 _) (hb.1 _)) (andUp _ _ _ _ (ha.1 _) (hb.1 _))
        split
        · exact orUp _ _ _ _ (andUp _ _ _ _ (ha.1 _) (hb.1 _)) (andUp _ _ _ _ (ha.1 _) (hb.1 _))
        · exact andUp _ _ _ _ (ha.1 _) (hb.1 _)
      · intro t ht
        have h60 : t ≠ 60 := by intro h; subst t; contradiction
        have h61 : t ≠ 61 := by intro h; subst t; contradiction
        simp [mul,h60,h61,ha.2 t ht,hb.2 t ht]
    let masks : List ℕ := [0,3458764513820540929,2,16,64]
    let bits (m : ℕ) := fun t : Fin 62 => m.testBit t.val
    have catalogue : ∀ i j : Fin 14, i ≠ j →
        Nat.testBit 365118556550 (14 * min i.val j.val + max i.val j.val) = true →
        ∃ m ∈ masks, Keeps (bits m) (mul (fun t => input t i) (fun t => input t j)) := by
      dsimp only [masks,Keeps,bits,mul,input,base]
      decide +kernel
    have nz : 0 < C.size := by omega
    obtain ⟨ne,ltA,ltB,act⟩ := rules 0 nz
    let a : Fin 14 := ⟨opnd C 0 0,by omega⟩
    let b : Fin 14 := ⟨opnd C 0 1,by omega⟩
    obtain ⟨m,hm,hmul⟩ := catalogue a b (fun h => ne (congrArg Fin.val h)) orbit
    have v14 : V 14 = mul (V a.val) (V b.val) := by
      rcases act with act|act
      · exact act.2
      · exact GateOp.noConfusion (first.symm.trans act.1)
    have sound : Keeps (bits m) (V 14) := by rwa [v14,inputV a,inputV b]
    let init := seed ++ [bits m]
    have initLen : init.length=15 := by simp [init,seedLen]
    let z := fun _ : Fin 62 => false
    let target := fun t : Fin 62 => decide (t.val < 21)
    have initRel (i : ℕ) (hi : i<15) : Keeps (init.getD i z) (V i) := by
      by_cases h : i<14
      · rw [show init.getD i z = (seed++seq).getD i z by
              simp only [init,List.getD_append _ _ _ _ (show i<seed.length by omega)]]
        rw [show (seed++seq).getD i z = V i from publicWire i (by omega)]
        exact same _
      · have e : i=14 := by omega
        subst i
        have eq : init.getD 14 z = bits m := by
          change (seed++[bits m]).getD 14 _ = _
          rw [← seedLen]; simp
        rw [eq]; exact sound
    let legal (S : List (Fin 62 → Bool)) (j : ℕ) : Prop :=
      ∃ a b : ℕ, a ≠ b ∧ a < 15+j ∧ b < 15+j ∧
        (S.getD j z = add ((init++S).getD a z) ((init++S).getD b z) ∨
         S.getD j z = mul ((init++S).getD a z) ((init++S).getD b z))
    have constructTail : ∀ k : ℕ, k+1 ≤ C.size →
        ∃ S : List (Fin 62 → Bool), S.length=k ∧ (∀ j<k, legal S j) ∧
          ∀ i<15+k, Keeps ((init++S).getD i z) (V i) := by
      intro k
      induction k with
      | zero =>
        intro _
        exact ⟨[],rfl,fun j h => (Nat.not_lt_zero _ h).elim,by simpa using initRel⟩
      | succ k ih =>
        intro hk
        obtain ⟨S,hS,steps,sim⟩ := ih (by omega)
        let j := k+1
        let a := opnd C j 0
        let b := opnd C j 1
        obtain ⟨diff,ha,hb,choice⟩ := rules j (by dsimp [j];omega)
        have ea : a < 15+k := by dsimp [a,j] at *;omega
        have eb : b < 15+k := by dsimp [b,j] at *;omega
        let A := (init++S).getD a z
        let B := (init++S).getD b z
        have both := combine _ _ A B (sim a ea) (sim b eb)
        have build : ∃ u, (u=add A B ∨ u=mul A B) ∧ Keeps u (V (15+k)) := by
          have index : 15+k=14+j := by dsimp [j];omega
          rw [index]
          rcases choice with c|c
          · exact ⟨_,Or.inr rfl,c.2 ▸ both.2⟩
          · exact ⟨_,Or.inl rfl,c.2 ▸ both.1⟩
        obtain ⟨u,rule,hu⟩ := build
        let T := S ++ [u]
        have size : T.length = k+1 := by simp [T,hS]
        have keep (w : ℕ) (hw : w < 15+k) :
            (init++T).getD w z = (init++S).getD w z := by
          change (init++(S++[u])).getD w z = _
          rw [← List.append_assoc,List.getD_append _ _ _ _ (by simp [initLen,hS];omega)]
        have endS : T.getD k z = u := by rw [← hS];simp [T]
        refine ⟨T,size,?_,?_⟩
        · intro i hi
          by_cases old : i<k
          · obtain ⟨p,r,pr,ep,er,op⟩ := steps i old
            refine ⟨p,r,pr,ep,er,?_⟩
            have prev : T.getD i z = S.getD i z :=
              List.getD_append _ _ _ _ (by omega)
            rw [prev,keep p (by omega),keep r (by omega)]
            exact op
          · have eq : i=k := by omega
            subst i
            refine ⟨a,b,diff,ea,eb,?_⟩
            rwa [endS,keep a ea,keep b eb]
        · intro i hi
          by_cases old : i<15+k
          · rw [keep i old];exact sim i old
          · have eq : i=15+k := by omega
            subst i
            have atEnd : (init++T).getD (15+k) z = u := by
              rw [show 15+k=(init++S).length by simp [initLen,hS]]
              change (init++(S++[u])).getD (init++S).length z = u
              rw [← List.append_assoc];simp
            rwa [atEnd]
    have outLater : 15 ≤ C.output := by
      by_contra! small
      have eq : C.output=14 := by omega
      have h : Keeps (bits m) target := by simpa only [←eq,outValue] using sound
      have impossible : ∀ n ∈ masks, ¬Keeps (bits n) target := by
        dsimp only [masks,Keeps,bits,target];decide +kernel
      exact impossible m hm h
    obtain ⟨S,size,steps,values⟩ := constructTail (C.size-1) (by omega)
    have endRel := values C.output (by omega)
    rw [outValue] at endRel
    have exactValue : (init++S).getD C.output z = target := by
      funext t
      by_cases pos : t.val<21
      · exact endRel.2 t pos
      · cases e : (init++S).getD C.output z t with
        | false => simp [target,pos]
        | true => exact (by simpa [pos] using endRel.1 t e : False).elim
    have mem : target ∈ S := by
      have hi : C.output < (init++S).length := by simp [initLen,size];omega
      rw [List.getD_eq_getElem _ _ hi,List.getElem_append_right (by omega : init.length ≤ C.output)] at exactValue
      rw [← exactValue];exact List.getElem_mem ..
    have ok : ∀ j<S.length, legal S j := by simpa only [size] using steps
    rcases List.mem_cons.mp hm with e|edge
    · subst m
      apply withoutEdge
      refine ⟨S,by omega,mem,?_⟩
      have zeroBits : bits 0 = z := by funext t; simp [bits,z]
      simpa only [legal,init,zeroBits] using ok
    · apply withEdge m edge
      exact ⟨S,by omega,mem,ok⟩

  intro C hsize hm distinct first hfun hreads
  have hget (C : Circuit) (j : ℕ) (hj : j < C.size) : C.gates[j]? = some (gateAt C j) := by
    change C.gates[j]? = some (C.gates.getD j ⟨.or, []⟩)
    rw [List.getElem?_eq_getElem (show j < C.gates.length from hj),
      List.getD_eq_getElem _ _ (show j < C.gates.length from hj)]
  have hopnd (C : Circuit) (j a b : ℕ) (hab : (gateAt C j).inputs = [a, b]) :
      opnd C j 0 = a ∧ opnd C j 1 = b := by
    change (gateAt C j).inputs.getD 0 0 = a ∧ (gateAt C j).inputs.getD 1 0 = b
    rw [hab]
    exact ⟨rfl, rfl⟩
  have hg (j : ℕ) (g : Gate) (he : C.gates[j]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j := by
    have hj : j < C.size := by
      change j < C.gates.length
      exact List.getElem?_eq_some_iff.mp he |>.choose
    have mem := List.mem_of_getElem? he
    have len := hm.2.2 g mem
    obtain ⟨a,b,hab⟩ : ∃ a b, g.inputs = [a,b] := List.length_eq_two.mp len
    have eqg := Option.some.inj ((hget C j hj).symm.trans he)
    obtain ⟨ha,hb⟩ := hopnd C j a b (eqg ▸ hab)
    refine ⟨hm.1 g mem,a,b,hab,?_,?_,?_⟩
    · simpa [ha,hb] using distinct j hj
    · apply hm.2.1 j hj a
      change a ∈ (gateAt C j).inputs
      simp [eqg,hab]
    · apply hm.2.1 j hj b
      change b ∈ (gateAt C j).inputs
      simp [eqg,hab]
  have hgate (j : ℕ) (hj : j < C.size) :
      ∃ a b, (gateAt C j).inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j :=
    (hg j (gateAt C j) (hget C j hj)).2
  have pos : 0 < C.size := by
    by_contra! hz
    obtain ⟨gs,o⟩ := C
    have hnil : gs = [] := List.length_eq_zero_iff.mp (by change gs.length ≤ 0 at hz; omega)
    subst gs
    let x : Fin 14 → Bool := fun i => decide (i.val = o)
    have h := hfun x
    by_cases ho : o < 14
    · have yes : (Circuit.mk [] o).eval (List.ofFn x) = true := by
        change (List.ofFn x).getD o false = true
        rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
        simp [ho,x]
      obtain ⟨u,t,_,hu,ht⟩ := h.mp yes
      simp [x] at hu ht
      omega
    · have h := (hfun (fun _ => true)).2 ⟨0,0,Or.inl rfl,rfl,rfl⟩
      change (List.ofFn (fun _ : Fin 14 => true)).getD o false = true at h
      rw [List.getD_eq_default _ false (by simp; omega)] at h
      contradiction
  obtain ⟨a,b,hab,hn,ha,hb⟩ := hgate 0 pos
  let A : Fin 14 := ⟨a,by omega⟩
  let B : Fin 14 := ⟨b,by omega⟩
  let edge (i j : Fin 14) : Prop := ∃ p l : Fin 7,
    (p = l ∨ p = l+1 ∨ p = l+3) ∧
    ((i = Fin.castAdd 7 p ∧ j = Fin.natAdd 7 l) ∨
     (j = Fin.castAdd 7 p ∧ i = Fin.natAdd 7 l))
  -- The even rows fix both marked inputs and the odd rows interchange them.
  let maps : Fin 16 → Fin 14 → Fin 14 :=
    ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13],
      ![7,13,12,11,10,9,8,0,6,5,4,3,2,1],
      ![0,1,4,3,2,6,5,7,8,10,9,13,12,11],
      ![7,13,10,11,12,8,9,0,6,4,5,1,2,3],
      ![0,1,5,3,6,2,4,7,12,9,10,13,8,11],
      ![7,13,9,11,8,12,10,0,2,5,4,1,6,3],
      ![0,1,6,3,5,4,2,7,12,10,9,11,8,13],
      ![7,13,8,11,9,10,12,0,2,4,5,3,6,1],
      ![0,3,2,1,5,4,6,7,9,8,12,11,10,13],
      ![7,11,12,13,9,10,8,0,5,6,2,3,4,1],
      ![0,3,4,1,6,2,5,7,10,8,12,13,9,11],
      ![7,11,10,13,8,12,9,0,4,6,2,1,5,3],
      ![0,3,5,1,2,6,4,7,9,12,8,13,10,11],
      ![7,11,9,13,12,8,10,0,5,2,6,1,4,3],
      ![0,3,6,1,4,5,2,7,10,12,8,11,9,13],
      ![7,11,8,13,10,9,12,0,4,2,6,3,5,1]]
  let adjacent (i j : Fin 14) : Bool :=
    let p := min i.val j.val
    let l := max i.val j.val - 7
    decide (p < 7 ∧ 7 ≤ max i.val j.val ∧ (p = l ∨ p = (l+1)%7 ∨ p = (l+3)%7))
  have edgeTest : ∀ i j, edge i j ↔ adjacent i j = true := by
    dsimp only [edge, adjacent]
    decide +kernel
  have cert : (∀ k : Fin 16, let f := maps k; (∀ x y, f x = f y → x = y) ∧
      (∀ x y, adjacent (f x) (f y) = adjacent x y) ∧
      ((f 0 = 0 ∧ f 7 = 7) ∨ (f 0 = 7 ∧ f 7 = 0))) ∧
      ∀ i j : Fin 14, i ≠ j → ∃ k : Fin 16, let f := maps k
      Nat.testBit 365118556550 (14 * min (f i).val (f j).val + max (f i).val (f j).val) = true := by
    dsimp only [adjacent,maps]
    decide +kernel
  obtain ⟨k,rep⟩ := cert.2 A B (fun e => hn (congrArg Fin.val e))
  obtain ⟨hi,hAdj,flag⟩ := cert.1 k
  have preserve (i j : Fin 14) : edge (maps k i) (maps k j) ↔ edge i j := by
    rw [edgeTest, edgeTest, hAdj]
  let σ := Equiv.ofBijective (maps k) (Finite.injective_iff_bijective.mp hi)
  let τ := σ.symm
  -- Relabel the input wires and keep each gate's wire number.
  let M (ρ : Equiv.Perm (Fin 14)) (w : ℕ) : ℕ :=
    if h : w < 14 then (ρ ⟨w, h⟩).val else w
  have hMlt (ρ : Equiv.Perm (Fin 14)) (i : ℕ) : M ρ i < 14 ↔ i < 14 := by
    by_cases h : i < 14
    · simp only [M, dite_eq_left h, h, iff_true]
      exact (ρ ⟨i, h⟩).isLt
    · simp [M, h]
  have hMof (ρ : Equiv.Perm (Fin 14)) (i : Fin 14) : M ρ i.val = (ρ i).val := by
    simp [M, i.isLt]
  have hMinv (ρ : Equiv.Perm (Fin 14)) (i : ℕ) : M ρ.symm (M ρ i) = i := by
    by_cases h : i < 14
    · let j : Fin 14 := ⟨i, h⟩
      change M ρ.symm (M ρ j.val) = j.val
      rw [hMof, hMof, ρ.symm_apply_apply]
    · simp [M, h]
  have hMbound (ρ : Equiv.Perm (Fin 14)) (i j : ℕ) (h : i < 14 + j) : M ρ i < 14 + j := by
    by_cases hi : i < 14
    · have := (hMlt ρ i).2 hi
      omega
    · simpa [M, hi] using h
  let mapGate (ρ : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (M ρ)⟩
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have evalRel (ρ : Equiv.Perm (Fin 14)) (gs : List Gate) :
      ∀ W W' : List Bool, 14 ≤ W.length → W'.length = W.length →
        (∀ w, W'.getD (M ρ w) false = W.getD w false) →
        ∀ w, ((gs.map (mapGate ρ)).foldl step W').getD (M ρ w) false =
          (gs.foldl step W).getD w false := by
    induction gs with
    | nil => intro W W' hW hlen hbase w; exact hbase w
    | cons g gs ih =>
      intro W W' hW hlen hbase w
      simp only [List.map_cons, List.foldl_cons]
      have hv : (mapGate ρ g).op.eval ((mapGate ρ g).inputs.map fun i => W'.getD i false) =
          g.op.eval (g.inputs.map fun i => W.getD i false) := by
        simp only [mapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hbase a
      apply ih (step W g) (step W' (mapGate ρ g)) (by simp [step]; omega)
        (by simp [step, hlen]) _ w
      intro u
      simp only [step, hv]
      rcases Nat.lt_trichotomy u W.length with hlt | heq | hgt
      · have hlt' : M ρ u < W'.length := by
          by_cases hsmall : u < 14
          · have := (hMlt ρ u).2 hsmall
            omega
          · simpa [M, hsmall, hlen] using hlt
        rw [List.getD_append _ _ _ _ hlt', List.getD_append _ _ _ _ hlt]
        exact hbase u
      · have hlarge : ¬ u < 14 := by omega
        rw [show M ρ u = u by simp [M, hlarge]]
        have last (w : List Bool) (x : Bool) (h : u = w.length) :
            (w ++ [x]).getD u false = x := by rw [h]; simp
        rw [last W' _ (by omega), last W _ heq]
      · have hlarge : ¬ u < 14 := by omega
        rw [show M ρ u = u by simp [M, hlarge],
          List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
  have hWires (ρ : Equiv.Perm (Fin 14)) (C : Circuit) (x : Fin 14 → Bool) (w : ℕ) :
      ((Circuit.mk (C.gates.map (mapGate ρ)) (M ρ C.output)).wires (List.ofFn x)).getD
        (M ρ w) false = (C.wires (List.ofFn (x ∘ ρ))).getD w false := by
    apply evalRel ρ C.gates _ _ (by simp) (by simp) _ w
    intro i
    by_cases h : i < 14
    · let j : Fin 14 := ⟨i, h⟩
      change (List.ofFn x).getD (M ρ j.val) false = (List.ofFn (x ∘ ρ)).getD j.val false
      rw [hMof]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (ρ j).isLt),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),
          List.getElem_ofFn, List.getElem_ofFn]
      rfl
    · rw [show M ρ i = i by simp [M, h],
        List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  let D : Circuit := ⟨C.gates.map (mapGate σ), M σ C.output⟩
  have hDsize : D.size = C.size := List.length_map (mapGate σ)
  have hDget (j : ℕ) : D.gates[j]? = C.gates[j]?.map (mapGate σ) := List.getElem?_map
  have hDgate (j : ℕ) (hj : j < D.size) :
      gateAt D j = mapGate σ (gateAt C j) := by
    have hj' : j < C.size := hDsize ▸ hj
    have h := hDget j
    rw [hget D j hj, hget C j hj'] at h
    exact Option.some.inj h
  have hDinputs (j a b : ℕ) (hj : j < D.size) (hab : (gateAt C j).inputs = [a, b]) :
      (gateAt D j).inputs = [M σ a, M σ b] := by
    rw [hDgate j hj]
    change (gateAt C j).inputs.map (M σ) = _
    rw [hab]
    rfl
  have hDmono : IsAO2 14 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hmem
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hmem
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg'
      exact (hg j g' hj).1
    · intro j hj i hi
      obtain ⟨a, b, hab, _, ha, hb⟩ := hgate j (hDsize ▸ hj)
      rw [hDinputs j a b hj hab] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hMbound σ a j ha
      · exact hMbound σ b j hb
    · intro g hmem
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hmem
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg'
      obtain ⟨a, b, hab, _⟩ := (hg j g' hj).2
      change (g'.inputs.map (M σ)).length = 2
      simp [hab]
  have hDdistinct (j : ℕ) (hj : j < D.size) : opnd D j 0 ≠ opnd D j 1 := by
    obtain ⟨a, b, hab, hn, _⟩ := hgate j (hDsize ▸ hj)
    obtain ⟨ha, hb⟩ := hopnd D j (M σ a) (M σ b) (hDinputs j a b hj hab)
    rw [ha, hb]
    intro he
    exact hn (by simpa only [hMinv] using congrArg (M σ.symm) he)
  have hDfun (x : Fin 14 → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    have alt (y : Fin 14 → Bool) : (∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
        y (Fin.castAdd 7 p) = true ∧ y (Fin.natAdd 7 l) = true) ↔
        ∃ i j, edge i j ∧ y i = true ∧ y j = true := by
      constructor
      · rintro ⟨p,l,h,hp,hl⟩
        exact ⟨_,_,⟨p,l,h,Or.inl ⟨rfl,rfl⟩⟩,hp,hl⟩
      · rintro ⟨i,j,⟨p,l,h,e⟩,hi',hj'⟩
        rcases e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact ⟨p,l,h,by assumption,by assumption⟩
    have he : D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) := hWires σ C x C.output
    rw [he,hfun,alt,alt]
    constructor
    · rintro ⟨i,j,h,hi',hj'⟩
      exact ⟨σ i,σ j,(preserve i j).2 h,hi',hj'⟩
    · rintro ⟨i,j,h,hi',hj'⟩
      obtain ⟨i,rfl⟩ := σ.surjective i
      obtain ⟨j,rfl⟩ := σ.surjective j
      exact ⟨i,j,(preserve i j).1 h,hi',hj'⟩
  have hdpos : 0 < D.size := hDsize ▸ pos
  have hfirst : (gateAt D 0).op = .and := by rw [hDgate 0 hdpos]; exact first
  obtain ⟨dfa,dfb⟩ := hopnd D 0 _ _ (hDinputs 0 a b hdpos hab)
  apply canonical D (by omega) hDmono hDdistinct hfirst hDfun
  ·
    dsimp only
    rw [dfa,dfb]
    change Nat.testBit _ (14 * min (M σ A.val) (M σ B.val) + max (M σ A.val) (M σ B.val)) = true
    rw [hMof,hMof]
    exact rep
  intro s

  obtain ⟨t,base,seed⟩ : ∃ t : Bool,
      σ (if t then 0 else 7) = (if s then 0 else 7) ∧
      σ (if t then 7 else 0) = (if s then 7 else 0) := by
    rcases flag with f | f
    · exact ⟨s,by cases s <;> first | exact f.1 | exact f.2,by cases s <;> first | exact f.1 | exact f.2⟩
    · exact ⟨!s,by cases s <;> first | exact f.1 | exact f.2,by cases s <;> first | exact f.1 | exact f.2⟩
  obtain ⟨z,hzinit,hzgate,hzout⟩ := hreads t
  let x : Fin 14 → Bool := fun i => decide (i = if s then 0 else 7)
  have hx : x ∘ σ = fun i : Fin 14 => decide (i = if t then 0 else 7) := by
    funext i
    apply Bool.decide_congr
    change σ i = _ ↔ _
    rw [← base, σ.injective.eq_iff]
  have hW (i : ℕ) : (D.wires (List.ofFn x)).getD (M σ i) false =
      (C.wires (List.ofFn (fun i : Fin 14 => decide (i = if t then 0 else 7)))).getD i false := by
    rw [← hx]
    exact hWires σ C x i
  have hseed : M σ (if t then 7 else 0) = if s then 7 else 0 := by
    have h := congrArg Fin.val seed
    cases s <;> cases t <;> simpa [M,σ] using h
  refine ⟨fun i => z (M τ i), ?_, ?_, ?_⟩
  · intro i hi
    change z (M τ i) = decide (i = if s then 7 else 0)
    rw [hzinit _ ((hMlt τ i).2 hi)]
    apply Bool.decide_congr
    constructor
    · intro he
      have he' := congrArg (M σ) he
      change M τ.symm (M τ i) = M σ _ at he'
      rwa [hMinv, hseed] at he'
    · intro he
      have he' := congrArg (M τ) (he.trans hseed.symm)
      change M τ i = M σ.symm (M σ _) at he'
      rwa [hMinv] at he'
  · intro j hj
    have hj' : j < C.size := hDsize ▸ hj
    obtain ⟨a, b, hab, _⟩ := hgate j hj'
    obtain ⟨ha, hb⟩ := hopnd C j a b hab
    obtain ⟨hda, hdb⟩ := hopnd D j (M σ a) (M σ b) (hDinputs j a b hj hab)
    have hOp : (gateAt D j).op = (gateAt C j).op := by rw [hDgate j hj]
    have hwire : M τ (14 + j) = 14 + j := by simp [M, show ¬ 14 + j < 14 by omega]
    have hma : M τ (M σ a) = a := hMinv σ a
    have hmb : M τ (M σ b) = b := hMinv σ b
    have hh := hzgate j hj'
    simp only [ha, hb] at hh
    change ((gateAt D j).op = GateOp.and → z (M τ (14 + j)) =
        (((D.wires (List.ofFn x)).getD (opnd D j 0) false && z (M τ (opnd D j 1))) ||
         (z (M τ (opnd D j 0)) && (D.wires (List.ofFn x)).getD (opnd D j 1) false))) ∧
      ((gateAt D j).op = GateOp.or → z (M τ (14 + j)) =
        (z (M τ (opnd D j 0)) || z (M τ (opnd D j 1))))
    simpa only [hOp, hda, hdb, hwire, hma, hmb, hW] using hh
  · change z (M σ.symm (M σ C.output)) = false
    rwa [hMinv]
