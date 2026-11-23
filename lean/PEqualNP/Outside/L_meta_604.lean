import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.Helpers.ReadersExport

namespace PEqualNP.Outside.L_meta_604

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers

private def xorGates (flip : Bool) (width i j : ℕ) : List Gate :=
  if flip then
    [⟨.or, [i, j]⟩, ⟨.and, [i, j]⟩, ⟨.not, [width]⟩,
      ⟨.or, [width + 1, width + 2]⟩]
  else
    [⟨.or, [i, j]⟩, ⟨.and, [i, j]⟩, ⟨.not, [width + 1]⟩,
      ⟨.and, [width, width + 2]⟩]

private theorem xorGates_eval (flip : Bool) (w : List Bool) (i j : ℕ)
    (hi : i < w.length) (hj : j < w.length) :
    (wiresFrom (xorGates flip w.length i j) w).getD (w.length + 3) false =
      xor (w.getD i false) (xor flip (w.getD j false)) := by
  have hprefix (tail : List Bool) (k : ℕ) (hk : k < w.length) :
      (w ++ tail)[k]?.getD false = w[k]?.getD false := by
    rw [List.getElem?_append_left hk]
  cases flip <;> simp [xorGates, wiresFrom, GateOp.eval, hprefix _ _ hi, hprefix _ _ hj] <;>
    cases w[i]?.getD false <;> cases w[j]?.getD false <;> rfl

private theorem appendXor (n s : ℕ) (g : (Fin n → Bool) → Bool) (flip : Bool)
    (hne : ∃ y y', g y ≠ g y') (hc : HasCircuitSize n g s) :
    HasCircuitSize (n + 1)
      (fun x => xor (x (Fin.last n)) (xor flip (g (fun i : Fin n => x i.castSucc)))) (s + 4) := by
  have lifted : HasCircuitSize (n + 1) (fun x => g (fun i : Fin n => x i.castSucc)) s :=
    PermInputs.relabel_size Fin.castSucc g s hc
  obtain ⟨C, hOk, hsz, heval⟩ := lifted
  let width := n + 1 + C.gates.length
  have width_eq (x : Fin (n + 1) → Bool) : (wiresFrom C.gates (List.ofFn x)).length = width := by
    simp [width, length_wiresFrom]
  have ho : C.output < width := by
    by_contra hn
    have hz (y : Fin n → Bool) : g y = false := by
      have he := heval (Fin.snoc y false)
      rw [Circuit.eval, wires_eq, List.getD_eq_default _ _ (by rw [width_eq]; omega)] at he
      simpa using he.symm
    obtain ⟨y, y', hyy'⟩ := hne
    exact hyy' ((hz y).trans (hz y').symm)
  refine ⟨⟨C.gates ++ xorGates flip width n C.output, width + 3⟩, ?_, ?_, ?_⟩
  · intro gate hgate
    rcases List.mem_append.1 hgate with h | h
    · exact hOk gate h
    · cases flip <;> simp only [xorGates, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at h <;>
        rcases h with rfl | rfl | rfl | rfl <;> simp
  · have hlen : C.gates.length ≤ s := hsz
    cases flip <;> simp [Circuit.size, xorGates] <;> omega
  · intro x
    let w := wiresFrom C.gates (List.ofFn x)
    have hw : w.length = width := width_eq x
    have hi : n < w.length := by rw [hw]; dsimp [width]; omega
    have hj : C.output < w.length := by rwa [hw]
    have hfresh : w.getD n false = x (Fin.last n) := by
      change (wiresFrom C.gates (List.ofFn x)).getD n false = _
      rw [getD_wiresFrom _ _ _ (by simp)]
      exact getD_ofFn (n + 1) x false (Fin.last n)
    have hbase : w.getD C.output false = g (fun i : Fin n => x i.castSucc) := heval x
    change (wiresFrom (C.gates ++ xorGates flip width n C.output) (List.ofFn x)).getD
      (width + 3) false = _
    rw [wiresFrom_append]
    change (wiresFrom (xorGates flip width n C.output) w).getD (width + 3) false = _
    rw [← hw, xorGates_eval flip w n C.output hi hj, hfresh, hbase]

private theorem upperBound (n s : ℕ) (g : (Fin n → Bool) → Bool)
    (hne : ∃ y y', g y ≠ g y')
    (hc : HasCircuitSize n g s ∨ HasCircuitSize n (fun y => !(g y)) s) :
    HasCircuitSize (n + 1) (fun x => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4) := by
  rcases hc with h | h
  · simpa using appendXor n s g false hne h
  · have hne' : ∃ y y', (!(g y)) ≠ (!(g y')) := by
      obtain ⟨y, y', hy⟩ := hne
      exact ⟨y, y', by simpa using hy⟩
    simpa using appendXor n s (fun y => !(g y)) true hne' h

open PEqualNP.MetaComplexity.Helpers.Readers

private theorem twoTouchedOutside {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    {gs : List Gate} {o : ℕ} (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b))
    (hflip : ∀ u, f (Function.update u i (!u i)) ≠ f u)
    (B : ℕ → Prop) (hi : B i) (hB : ∀ a, B a → IsC n gs i b a) :
    ∃ p q, p ≠ q ∧ ¬ B (n + 1 + p) ∧ ¬ B (n + 1 + q) ∧
      RC n gs i b p ∧ RC n gs i b q := by
  have hfnc : ∃ x y, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have hout : ∀ c, stF n gs i b o ≠ Stat.const c := by
    intro c hc
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    exact (restr_const L.hcl L.hev i b c hc x).trans (restr_const L.hcl L.hev i b c hc y).symm
  have reader (S : ℕ → Prop) (hiS : S i) (hoS : ¬ S o) :
      ∃ p gate, gs[p]? = some gate ∧ ¬ S (n + 1 + p) ∧ ∃ a ∈ gate.inputs, S a := by
    apply exists_reader (n + 1) i S hiS gs o hoS
    by_contra hsupport
    apply hflip (fun _ => false)
    rw [← L.hev, ← L.hev]
    exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have hk' : k ≠ i := fun e => hsupport (e ▸ hk)
        simp [Function.update_of_ne hk'])
  have ho : ¬ B o := fun h => by
    obtain ⟨c, hc⟩ := hB o h
    exact hout c hc
  obtain ⟨p, gp, hgp, hp, a, ha, haB⟩ := reader B hi ho
  have rp : RC n gs i b p := ⟨gp, hgp, a, ha, hB a haB⟩
  by_cases hsecond : ∃ q gq, q ≠ p ∧ gs[q]? = some gq ∧ ¬ B (n + 1 + q) ∧ ∃ c ∈ gq.inputs, B c
  · obtain ⟨q, gq, hne, hgq, hq, c, hc, hcB⟩ := hsecond
    exact ⟨p, q, hne.symm, hp, hq, rp, ⟨gq, hgq, c, hc, hB c hcB⟩⟩
  by_cases hpconst : IsC n gs i b (n + 1 + p)
  · obtain ⟨q, gq, hgq, hq, c, hc, hcB⟩ := reader (fun k => B k ∨ k = n + 1 + p)
      (Or.inl hi) (fun h => h.elim ho (fun e => by
        obtain ⟨v, hv⟩ := hpconst
        exact hout v (by rw [e]; exact hv)))
    refine ⟨p, q, fun e => hq (Or.inr (by rw [e])), hp, fun h => hq (Or.inl h), rp,
      gq, hgq, c, hc, ?_⟩
    rcases hcB with h | e
    · exact hB c h
    · rw [e]; exact hpconst
  · exfalso
    obtain ⟨c, hc⟩ := hB a haB
    obtain ⟨hop, _, w, hw, hwn⟩ := st_shape n gs L.hcl i b p gp hgp a ha c hc
      (fun c' h => hpconst ⟨c', h⟩)
    have hwB : ¬ B w := fun h => by
      obtain ⟨v, hv⟩ := hB w h
      exact hwn v hv
    have hwlt := (L.hcl p gp hgp).lt w hw
    have hpLen := (List.getElem?_eq_some_iff.1 hgp).1
    obtain ⟨u, hu⟩ := takes gs (fun k _ hk v => L.no_const hfnc k (List.getElem?_eq_some_iff.1 hk).1 v)
      w (by omega) (fixBit gp)
    apply hflip u
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
    · intro j hj hjB
      rw [vl_input gs _ j hj, vl_input gs _ j hj]
      exact Function.update_of_ne
        (fun e => hjB (by rw [show j = (i : ℕ) from congrArg Fin.val e]; exact hi)) _ _
    · intro q gq hgq _ hq hr hagree
      obtain ⟨a', ha', ha'B⟩ := hr
      have eq : q = p := by
        by_contra hne
        exact hsecond ⟨q, gq, hne, hgq, hq, a', ha', ha'B⟩
      rw [eq] at hagree ⊢
      rw [vl_abs gs L.hcl _ p gp hgp hop w hw (by rw [hagree w hwlt hwB]; exact hu),
        vl_abs gs L.hcl u p gp hgp hop w hw hu]

private theorem dropThree {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    (i : Fin (n + 1)) (hflip : ∀ u, f (Function.update u i (!u i)) ≠ f u)
    (hnc : ∀ b, ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b))
    (hc : HasCircuitSize (n + 1) f s) : ∃ b, Drop f i b 3 s := by
  have hd : Dep f i := ⟨fun _ => false, hflip _⟩
  obtain ⟨gs, o, L, hsz⟩ := exists_least (n + 1) f s (dep_nc hd) hc
  obtain ⟨p, gp, hgp, hp⟩ := L.dep_read i hd hnc
  let b := fixBit gp
  have hpC : IsC n gs i b (n + 1 + p) := isC_reader L.hcl i p gp hgp hp b (Or.inr rfl)
  have hB : ∀ a, a = (i : ℕ) ∨ a = n + 1 + p → IsC n gs i b a := by
    rintro a (rfl | rfl)
    · exact ⟨b, stF_self n gs i b⟩
    · exact hpC
  obtain ⟨q, r, hqr, hq, hr, rq, rr⟩ := twoTouchedOutside L i b (hnc b) hflip
    (fun a => a = (i : ℕ) ∨ a = n + 1 + p) (Or.inl rfl) hB
  have hpq : p ≠ q := fun e => hq (Or.inr (by rw [e]))
  have hpr : p ≠ r := fun e => hr (Or.inr (by rw [e]))
  exact ⟨b, (L.save3 i b (hnc b) p q r hpq hpr hqr (rc_input b ⟨gp, hgp, hp⟩) rq rr).mono le_rfl hsz⟩

private theorem lowerBoundThree (n s : ℕ) (g : (Fin n → Bool) → Bool)
    (hne : ∃ y y', g y ≠ g y')
    (hc : HasCircuitSize (n + 1) (fun x => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 3)) :
    HasCircuitSize n g s ∨ HasCircuitSize n (fun y => !(g y)) s := by
  let f := fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))
  have hlast (x : Fin (n + 1) → Bool) (b : Bool) :
      f (Function.update x (Fin.last n) b) = xor b (g (fun i : Fin n => x i.castSucc)) := by
    have rest : (fun i : Fin n => Function.update x (Fin.last n) b i.castSucc) =
        (fun i : Fin n => x i.castSucc) := by
      funext i
      rw [Function.update_of_ne]
      intro he
      have hn := congrArg Fin.val he
      have hi := i.isLt
      simp at hn
      omega
    change xor ((Function.update x (Fin.last n) b) (Fin.last n))
      (g (fun i : Fin n => Function.update x (Fin.last n) b i.castSucc)) = _
    rw [Function.update_self, rest]
  have hflip (x : Fin (n + 1) → Bool) :
      f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x := by
    rw [hlast]
    change xor (!x (Fin.last n)) (g (fun i : Fin n => x i.castSucc)) ≠
      xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))
    cases x (Fin.last n) <;> cases g (fun i : Fin n => x i.castSucc) <;> decide
  have nc (b : Bool) : ∃ x y, f (Function.update x (Fin.last n) b) ≠ f (Function.update y (Fin.last n) b) := by
    obtain ⟨y, y', hy⟩ := hne
    refine ⟨Fin.snoc y false, Fin.snoc y' false, ?_⟩
    rw [hlast, hlast]
    cases b <;> simpa using hy
  have hn : 0 < n := by
    by_contra h
    have ez : n = 0 := by omega
    subst n
    obtain ⟨y, y', hy⟩ := hne
    exact hy (congrArg g (Subsingleton.elim y y'))
  let ρ : Fin (n + 1) → Fin n := fun j => if hj : j.val < n then ⟨j.val, hj⟩ else ⟨0, hn⟩
  have hρ (i : Fin n) : ρ i.castSucc = i := by
    simp [ρ, i.isLt]
  obtain ⟨b, t, ht, hbd⟩ := dropThree (Fin.last n) hflip nc hc
  obtain ⟨C, hok, hsize, heval⟩ := PermInputs.relabel_size ρ _ t hbd
  have hlen : C.size ≤ s := by omega
  have hval (y : Fin n → Bool) : C.eval (List.ofFn y) = xor b (g y) := by
    rw [heval]
    change f (Function.update (y ∘ ρ) (Fin.last n) b) = xor b (g y)
    rw [hlast]
    have hy : (fun i : Fin n => (y ∘ ρ) i.castSucc) = y := by
      funext i
      exact congrArg y (hρ i)
    rw [hy]
  cases b
  · exact Or.inl ⟨C, hok, hlen, fun y => by simpa using hval y⟩
  · exact Or.inr ⟨C, hok, hlen, fun y => by simpa using hval y⟩

end PEqualNP.Outside.L_meta_604
