module NormalForms where

open import Syntax

open import Data.Nat hiding (_<_)
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)


mutual 
  data Nf (Γ : Con) : Ty → Set where
    nlam  : ∀{σ τ} → Nf (Γ < σ) τ → Nf Γ (σ ⇒ τ)
    ne    : Ne Γ ι → Nf Γ ι
    nenat : Ne Γ nat → Nf Γ nat
    _,-,_ : ∀{σ τ} → Nf Γ σ → Nf Γ τ → Nf Γ (σ ∧ τ)
    nze   : Nf Γ nat
    nsu   : Nf Γ nat → Nf Γ nat
    nunf  : ∀{σ} → Nf Γ σ → Nf Γ (σ ⇒ σ) → Nf Γ < σ > 
   
  data Ne (Γ : Con) : Ty → Set where
    nvar  : ∀{σ} → Var Γ σ → Ne Γ σ
    napp  : ∀{σ τ} → Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ
    nfst  : ∀{σ τ} → Ne Γ (σ ∧ τ) → Ne Γ σ
    nsnd  : ∀{σ τ} → Ne Γ (σ ∧ τ) → Ne Γ τ
    nrec  : ∀{σ} → Nf Γ σ  → Nf Γ (σ ⇒ σ) → Ne Γ nat → Ne Γ σ 
    nsh   : ∀{σ} → Ne Γ < σ > → Ne Γ σ
    nst   : ∀{σ} → Ne Γ < σ > → Ne Γ < σ >


mutual
  embNf : ∀{Γ σ} → Nf Γ σ → Tm Γ σ
  embNf (nlam n) = lam (embNf n)
  embNf (ne x) = embNe x
  embNf (nenat x) = embNe x
  embNf (a ,-, b) = embNf a ,, embNf b
  embNf nze = ze
  embNf (nsu n) = su (embNf n)
  embNf (nunf x f) = unf (embNf x) (embNf f)

  embNe : ∀{Γ σ} → Ne Γ σ → Tm Γ σ
  embNe (nvar x) = var x
  embNe (napp t u) = app (embNe t) (embNf u)
  embNe (nfst n) = fst (embNe n)
  embNe (nsnd n) = snd (embNe n)
  embNe (nrec z f n) = rec (embNf z) (embNf f) (embNe n)
  embNe (nsh s) = sh (embNe s)
  embNe (nst s) = st (embNe s)


mutual
  renNf : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Nf Δ σ → Nf Γ σ
  renNf α (nlam n) = nlam (renNf (wk α) n)
  renNf α (ne n) = ne (renNe α n)
  renNf α (nenat n) = nenat (renNe α n)
  renNf α (a ,-, b) = renNf α a ,-, renNf α b
  renNf α nze = nze
  renNf α (nsu n) = nsu (renNf α n)
  renNf α (nunf x f) = nunf (renNf α x) (renNf α f)

  renNe : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Ne Δ σ → Ne Γ σ
  renNe α (nvar x) = nvar (α x)
  renNe α (napp t u) = napp (renNe α t) (renNf α u)
  renNe α (nfst n) = nfst (renNe α n)
  renNe α (nsnd n) = nsnd (renNe α n)
  renNe α (nrec z f n) = nrec (renNf α z) (renNf α f) (renNe α n)
  renNe α (nsh s) = nsh (renNe α s)
  renNe α (nst s) = nst (renNe α s)



mutual
  rennecomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : Ne Γ σ) → renNe ρ' (renNe ρ v) ≅ renNe (ρ' ∘ ρ) v
  rennecomp ρ' ρ (nvar x) = refl
  rennecomp ρ' ρ (napp t u) = cong₂ napp (rennecomp ρ' ρ t) (rennfcomp ρ' ρ u)
  rennecomp ρ' ρ (nrec z f n) = cong₃ nrec (rennfcomp ρ' ρ z) (rennfcomp ρ' ρ f) (rennecomp ρ' ρ n)
  rennecomp ρ' ρ (nfst n) = cong nfst (rennecomp ρ' ρ n)
  rennecomp ρ' ρ (nsnd n) = cong nsnd (rennecomp ρ' ρ n)
  rennecomp ρ' ρ (nsh n) = cong nsh (rennecomp ρ' ρ n)
  rennecomp ρ' ρ (nst n) = cong nst (rennecomp ρ' ρ n)

  rennfcomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : Nf Γ σ) → renNf ρ' (renNf ρ v) ≅ renNf (ρ' ∘ ρ) v
  rennfcomp ρ' ρ (nlam v) = proof
    nlam (renNf (wk ρ') (renNf (wk ρ) v)) 
    ≅⟨ cong nlam (rennfcomp (wk ρ') (wk ρ) v) ⟩
    nlam (renNf (wk ρ' ∘ wk ρ) v) 
    ≅⟨ cong nlam (cong (λ (f : Ren _ _) → renNf f v) (iext (λ _ → ext (λ x → sym (wkcomp ρ' ρ x))))) ⟩
    nlam (renNf (wk (ρ' ∘ ρ)) v)
    ∎
  rennfcomp ρ' ρ (ne x) = cong ne (rennecomp ρ' ρ x)
  rennfcomp ρ' ρ (nenat x) = cong nenat (rennecomp ρ' ρ x)
  rennfcomp ρ' ρ nze = refl
  rennfcomp ρ' ρ (nsu v) = cong nsu (rennfcomp ρ' ρ v)
  rennfcomp ρ' ρ (a ,-, b) = cong₂ _,-,_ (rennfcomp ρ' ρ a) (rennfcomp ρ' ρ b)
  rennfcomp ρ' ρ (nunf x f) = cong₂ nunf (rennfcomp ρ' ρ x) (rennfcomp ρ' ρ f)


mutual
  rennfid : ∀{Γ σ} → (n : Nf Γ σ) → renNf renId n ≅ n
  rennfid (nlam n) = proof
    nlam (renNf (wk renId) n) 
    ≅⟨ cong (λ (f : Ren _ _) → nlam (renNf f n)) (iext λ σ' → ext λ x → wkid x) ⟩ 
    nlam (renNf renId n) 
    ≅⟨ cong nlam (rennfid n) ⟩ 
    nlam n
    ∎
  rennfid (ne x) = cong ne (renneid x)
  rennfid (nenat x) = cong nenat (renneid x)
  rennfid nze = refl
  rennfid (nsu n) = cong nsu (rennfid n)
  rennfid (a ,-, b) = cong₂ _,-,_ (rennfid a) (rennfid b)
  rennfid (nunf x f) = cong₂ nunf (rennfid x) (rennfid f)
  
  renneid : ∀{Γ σ} → (n : Ne Γ σ) → renNe renId n ≅ n
  renneid (nvar x) = refl
  renneid (napp t u) = cong₂ napp (renneid t) (rennfid u)
  renneid (nrec z f n) = cong₃ nrec (rennfid z) (rennfid f) (renneid n)
  renneid (nfst n) = cong nfst (renneid n)
  renneid (nsnd n) = cong nsnd (renneid n)
  renneid (nsh n) = cong nsh (renneid n)
  renneid (nst n) = cong nst (renneid n)


