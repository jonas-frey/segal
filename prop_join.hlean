import types.prod types.fin hit.pushout types.fiber homotopy.join 
       my_prelude types.pullback Spectral.homotopy.pushout
open is_trunc prod nat is_equiv function pushout eq equiv sigma 
     pullback trunc

infix ` ★ `:40 := join

section pushout_sigma

parameters {A : Type} {B C D : A → Type} (f : Πa, B a → C a) (g : Πa, B a → D a)
local abbreviation PS := pushout (total f) (total g)
local abbreviation SP := Σ a, pushout (f a) (g a)

definition PS_to_SP : PS → SP :=
begin
  intro p, induction p with c d b, 
  { induction c with a c, exact dpair a (inl c)},
  { induction d with a d, exact dpair a (inr d)},
  { induction b with a b, apply ap (dpair a), apply glue}  
end

definition SP_to_PS : SP → PS :=
begin
intro s, induction s with a p, 
  induction p with c d b,
  { apply inl, exact dpair a c},
  { apply inr, exact dpair a d},
  { apply glue}
end

definition sigma_rec_ap_dpair 
  {A C} {B:A→Type} (i : Π a (b : B a), C) {a} {b b' : B a} (p : b=b') 
  :  sigma.rec i ◅ (dpair a ◅ p) = i a ◅ p
  := begin induction p, reflexivity end

definition pushout_sigma : SP ≃ PS
  := begin 
     fapply equiv.MK SP_to_PS PS_to_SP,
     {
       intro b, induction b with a p, induction a with a c, reflexivity,
       induction p, reflexivity, induction x with a b, apply po_path, esimp,
       rewrite ap_id, 
       rewrite idp_con, 
       krewrite (ap_compose SP_to_PS), 
       krewrite elim_glue,
       krewrite sigma_rec_ap_dpair, 
       rewrite elim_glue, 
     },{
       intro s, induction s with a p, induction p with c d b, reflexivity, reflexivity, 
       apply po_path, 
       rewrite idp_con, 
       rewrite con_idp, 
       krewrite (ap_compose PS_to_SP),
       krewrite (ap_compose SP_to_PS),
       krewrite sigma_rec_ap_dpair, 
       krewrite elim_glue,
       krewrite elim_glue,
     }
     end
end pushout_sigma

definition prop_join_is_prop [instance] (X Y : Prop) : is_prop (X ★ Y) 
  := begin
       apply is_prop_of_imp_is_contr, intro, induction a, 
       { apply is_contr_equiv_closed, 
         { symmetry, 
           apply @pushout_of_equiv_right (X × Y) X Y pr1 
           begin 
             apply equiv.mk pr2, apply is_equiv_of_is_prop, intro,
             intro, fconstructor, assumption, assumption,
             intro, apply is_trunc_prod, exact _
           end
         },
         { 
           exact is_contr_of_inhabited_prop a _
         }
       },
       { apply is_contr_equiv_closed, 
         {    
           symmetry,
           fapply @pushout_of_equiv_left (X×Y) X Y 
           begin 
             apply equiv.mk pr1, apply is_equiv_of_is_prop, intro,
             intro, fconstructor, assumption, assumption,
             intro, apply is_trunc_prod, exact _
           end pr2,
         },
         { 
           exact is_contr_of_inhabited_prop a _
         }
       },
       apply is_prop.elim
     end

definition join_is_or (X Y : Prop) : X ∨ Y ≃ X ★ Y
  := begin
       fapply equiv.mk, intro, induction a, induction a with a b,
       exact inl a, exact inr b, 
       apply is_equiv_of_is_prop,
       intro, induction a, exact or.intro_left a, 
       exact or.intro_right a, apply is_prop.elim,
       exact _, exact _
     end

section or_pushout

parameters {A : Type} (φ ψ : A → Prop)
local abbreviation i1 : sigma (λ a, φ a × ψ a) → sigma φ := total (λa, pr1)
local abbreviation i2 : sigma (λ a, φ a × ψ a) → sigma ψ := total (λa, pr2)

-- TODO: get rid of symmetry
definition or_pushout : pushout i1 i2 ≃ sigma (λ a, φ a ∨ ψ a) 
 := begin symmetry,
    fapply equiv.trans, 
    { exact equiv.mk (sigma.total (λa, !join_is_or)) !is_equiv_total_of_is_fiberwise_equiv},
    { exact pushout_sigma _ _} 
    end

end or_pushout
