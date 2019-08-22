import types.fin .my_prelude

open nat fin function eq is_trunc

inductive ifin : ℕ → Type :=
| ifz : ∀{n}, ifin (succ n)
| ifs : ∀{n}, ifin n → ifin (succ n)

namespace ifin

open ifin fin nat nat.le

definition has_zero_ifin [instance] (n : ℕ) : has_zero (ifin $ succ n) :=
has_zero.mk ifz

definition emb {n} : ifin n → ifin (succ n):=
begin
intro i, induction i with n' n' i' IH, exact ifz, exact ifs IH,
end

definition maxi {n} : ifin (succ n) :=
begin
induction n with n' IH, exact 0, exact ifs IH,
end

definition fin_of_ifin [unfold 2] : ∀{n}, ifin n → fin n
| (succ n) ifz     := 0
| (succ n) (ifs i) := succ $ fin_of_ifin i

definition ifin_of_fin [reducible] : ∀{n}, fin n → ifin n
|  0        i              := elim0 i
| (succ n) (mk  0       x) := 0
| (succ n) (mk (succ i) x) := ifs $ ifin_of_fin $ mk i $ le_of_succ_le_succ x

-- definition succ_greater_zero (n : ℕ) [H : 

definition ifin_of_nat [coercion] {n : ℕ} [H : is_succ n] : ℕ → ifin n
   := λ i, ifin_of_fin (mk (i % n) begin apply mod_lt, induction H, apply zero_lt_succ end) 

definition ifs_to_succ {n} (i : ifin n) 
  :  fin_of_ifin (ifs i) = succ (fin_of_ifin i)
  := begin cases n, cases i, reflexivity end

definition succ_to_ifs {n} (i : fin n) 
  :  ifin_of_fin (succ i) = ifs (ifin_of_fin i)
  := begin 
     cases n, 
     { exact elim0 i},
     { induction i with i, exact ifs ◅ ifin_of_fin ◅ mk i ◅ !is_prop.elim}
     end

definition ifin_equiv_fin (n : ℕ) : ifin n ≃ fin n
:= begin
fapply equiv.MK fin_of_ifin ifin_of_fin, 
{ intro i, induction n with n' IH,
  { apply elim0},
  { induction i with i ltp,
    induction i with i' IH', 
    { apply eq_of_veq, reflexivity}, 
    { assert H : ifin_of_fin (mk (succ i') ltp) = ifs (ifin_of_fin $ mk i' $ lt_of_succ_lt_succ ltp), 
        reflexivity, rewrite H, apply eq_of_veq, unfold fin_of_ifin,rewrite IH, 
    },
  },
},
{ 
  intro i, induction i with n n i' IH,
  { reflexivity},
  { rewrite ifs_to_succ, rewrite succ_to_ifs, rewrite IH},
},
end

open function

--definition ifin_of_nat [coercion] {n} i [H : i < n] : ifin n := fin_to_ifin $ mk i H


definition ifin_code {n m} (i : ifin n) (j : ifin m) : Type.{0} :=
begin
induction i with n' n' i', 
{induction j with m' m' j', exact n' = m', exact empty},
{cases j with m' m' j', exact empty, exact Σ p : n' = m', i' =[p] j'}
end

definition ifin_encode {n m} (i : ifin n) (j : ifin m) (pair : Σ p : n = m, i =[p] j) : ifin_code i j
:= 
begin
induction pair with p q, induction q, induction i, unfold ifin_code, unfold ifin_code, fconstructor, reflexivity,
apply idpatho,
end

definition ifin_decode {n m} (i : ifin n) (j : ifin m) (c : ifin_code i j) : Σ p : n = m, i =[p] j
:= begin
induction i with n' n' i',
{induction j with m' m' j',
  { induction c, apply dpair rfl, apply idpatho},
  { induction c},
},
{induction j with m' m' m',
  { induction c},
  { induction c, induction a_1, fconstructor, reflexivity, apply idpatho},
}
end

definition code_equiv {n m} (i : ifin n) (j : ifin m) 
  : (ifin_code i j) ≃ (Σ p : n = m, i =[p] j)
  := begin 
fapply equiv.MK !ifin_decode !ifin_encode,  
intro c, induction c with p q, induction q, induction i, reflexivity,
reflexivity, intro a, 
induction i, induction j, induction a, reflexivity, induction a_1, induction j, induction a_1, induction a_1_1, induction a_3,
reflexivity,
end

end ifin
