{-# OPTIONS --copatterns #-}

module NormalForms where

open import Syntax

open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)



mutual 
  data Nf (Γ : Con) : Ty → Set where
    nlam    : ∀{σ τ} → Nf (Γ < σ) τ → Nf Γ (σ ⇒ τ)
    ne      : ∀{σ} → Ne Γ σ → Nf Γ σ
    _,-,_   : ∀{σ τ} → Nf Γ σ → Nf Γ τ → Nf Γ (σ ∧ τ)
    nze     : Nf Γ nat
    nsu     : Nf Γ nat → Nf Γ nat
    nstream : ∀{σ} → Nf Γ σ → ∞Nf<> Γ σ → Nf Γ < σ >
    nunfold : ∀{σ τ} → Nf Γ σ → Nf Γ (σ ⇒ σ ∧ τ) → Nf Γ < τ > 
   
  data Ne (Γ : Con) : Ty → Set where
    nvar : ∀{σ} → Var Γ σ → Ne Γ σ
    napp : ∀{σ τ} → Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ
    nfst : ∀{σ τ} → Ne Γ (σ ∧ τ) → Ne Γ σ
    nsnd : ∀{σ τ} → Ne Γ (σ ∧ τ) → Ne Γ τ
    nrec : ∀{σ} → Nf Γ σ  → Nf Γ (σ ⇒ σ) → Ne Γ nat → Ne Γ σ 
    nhd  : ∀{σ} → Ne Γ < σ > → Ne Γ σ
    ntl  : ∀{σ} → Ne Γ < σ > → Ne Γ < σ >

  record ∞Nf<> (Γ : Con)(σ : Ty) : Set where
    coinductive
    field nforce : Nf Γ < σ >

open ∞Nf<>

mutual
  data _Nf∼_ : ∀{Γ σ} → Nf Γ σ → Nf Γ σ → Set where
    nlam∼    : ∀{Γ σ τ} → {n n' : Nf (Γ < σ) τ} → n Nf∼ n' → (nlam n) Nf∼ (nlam n') 
    ne∼      : ∀{Γ σ} → {n n' : Ne Γ σ} → n Ne∼ n' → (ne n) Nf∼ (ne n')  
    _,∼,_    : ∀{Γ σ τ} → {a a' : Nf Γ σ}{b b' : Nf Γ τ} → a Nf∼ a' → b Nf∼ b' → (a ,-, b) Nf∼ (a' ,-, b') 
    nze∼     : ∀{Γ} → _Nf∼_ {Γ} nze nze 
    nsu∼     : ∀{Γ} → {n n' : Nf Γ nat} → n Nf∼ n' → (nsu n) Nf∼ (nsu n')
    nstream∼ : ∀{Γ σ} → {n n' : Nf Γ σ}{s s' : ∞Nf<> Γ σ} → n Nf∼ n' → s ∞Nf∼ s' → (nstream n s) Nf∼ (nstream n' s')  
    nunfold∼ : ∀{Γ σ τ} → {z z' : Nf Γ σ}{f f' : Nf Γ (σ ⇒ σ ∧ τ)} → z Nf∼ z' → f Nf∼ f' → (nunfold z f) Nf∼ (nunfold z' f')

  data _Ne∼_ : ∀{Γ σ} → Ne Γ σ → Ne Γ σ → Set where
    nvar∼ : ∀{Γ σ} → {x x' : Var Γ σ} → x ≅ x' → nvar x Ne∼ nvar x'
    napp∼ : ∀{Γ σ τ} → {t t' : Ne Γ (σ ⇒ τ)}{u u' : Nf Γ σ} → t Ne∼ t' → u Nf∼ u' → napp t u Ne∼ napp t' u'
    nfst∼ : ∀{Γ σ τ} → {p p' : Ne Γ (σ ∧ τ)} → p Ne∼ p' → nfst p Ne∼ nfst p' 
    nsnd∼ : ∀{Γ σ τ} → {p p' : Ne Γ (σ ∧ τ)} → p Ne∼ p' → nsnd p Ne∼ nsnd p' 
    nrec∼ : ∀{Γ σ} → {z z' : Nf Γ σ}{f f' : Nf Γ (σ ⇒ σ)}{n n' : Ne Γ nat} → z Nf∼ z' → f Nf∼ f' → n Ne∼ n' → nrec z f n Ne∼ nrec z' f' n' 
    nhd∼  : ∀{Γ σ} → {s s' : Ne Γ < σ >} → s Ne∼ s' → nhd s Ne∼ nhd s' 
    ntl∼  : ∀{Γ σ} → {s s' : Ne Γ < σ >} → s Ne∼ s' → ntl s Ne∼ ntl s' 

  record _∞Nf∼_ {Γ σ}(s s' : ∞Nf<> Γ σ) : Set where
    coinductive
    field ∼nforce : nforce s Nf∼ nforce s'

open _∞Nf∼_

mutual
  nf-refl : ∀{Γ σ} → {n : Nf Γ σ} → n Nf∼ n
  nf-refl {n = nlam n} = nlam∼ nf-refl
  nf-refl {n = ne x} = ne∼ ne-refl
  nf-refl {n = a ,-, b} = nf-refl ,∼, nf-refl
  nf-refl {n = nze} = nze∼
  nf-refl {n = nsu n} = nsu∼ nf-refl
  nf-refl {n = nstream n s} = nstream∼ nf-refl ∞nf-refl
  nf-refl {n = nunfold z f} = nunfold∼ nf-refl nf-refl

  ne-refl : ∀{Γ σ} → {n : Ne Γ σ} → n Ne∼ n
  ne-refl {n = nvar x} = nvar∼ refl
  ne-refl {n = napp t u} = napp∼ ne-refl nf-refl
  ne-refl {n = nfst n} = nfst∼ ne-refl
  ne-refl {n = nsnd n} = nsnd∼ ne-refl
  ne-refl {n = nrec z f n} = nrec∼ nf-refl nf-refl ne-refl
  ne-refl {n = nhd n} = nhd∼ ne-refl
  ne-refl {n = ntl n} = ntl∼ ne-refl
  
  ∞nf-refl : ∀{Γ σ} → {s : ∞Nf<> Γ σ} → s ∞Nf∼ s
  ∼nforce (∞nf-refl) = nf-refl

mutual
  nf-sym : ∀{Γ σ} → {n n' : Nf Γ σ} → n Nf∼ n' → n' Nf∼ n
  nf-sym (nlam∼ p) = nlam∼ (nf-sym p)
  nf-sym (ne∼ x) = ne∼ (ne-sym x)
  nf-sym (a ,∼, b) = nf-sym a ,∼, nf-sym b
  nf-sym nze∼ = nze∼
  nf-sym (nsu∼ p) = nsu∼ (nf-sym p)
  nf-sym (nstream∼ n s) = nstream∼ (nf-sym n) (∞nf-sym s)
  nf-sym (nunfold∼ z f) = nunfold∼ (nf-sym z) (nf-sym f)
  
  ne-sym : ∀{Γ σ} → {n n' : Ne Γ σ} → n Ne∼ n' → n' Ne∼ n
  ne-sym (nvar∼ x) = nvar∼ (sym x)
  ne-sym (napp∼ t u) = napp∼ (ne-sym t) (nf-sym u)
  ne-sym (nfst∼ p) = nfst∼ (ne-sym p)
  ne-sym (nsnd∼ p) = nsnd∼ (ne-sym p)
  ne-sym (nrec∼ z f n) = nrec∼ (nf-sym z) (nf-sym f) (ne-sym n)
  ne-sym (nhd∼ p) = nhd∼ (ne-sym p)
  ne-sym (ntl∼ p) = ntl∼ (ne-sym p)

  ∞nf-sym : ∀{Γ σ} → {n n' : ∞Nf<> Γ σ} → n ∞Nf∼ n' → n' ∞Nf∼ n
  ∼nforce (∞nf-sym p) = nf-sym (∼nforce p)

mutual
  nf-trans : ∀{Γ σ} → {k l m : Nf Γ σ} → k Nf∼ l → l Nf∼ m → k Nf∼ m
  nf-trans (nlam∼ p) (nlam∼ q) = nlam∼ (nf-trans p q)
  nf-trans (ne∼ p) (ne∼ q) = ne∼ (ne-trans p q)
  nf-trans (a ,∼, b) (a' ,∼, b') = nf-trans a a' ,∼, nf-trans b b'
  nf-trans nze∼ nze∼ = nze∼
  nf-trans (nsu∼ p) (nsu∼ q) = nsu∼ (nf-trans p q)
  nf-trans (nstream∼ n s) (nstream∼ n' s') = nstream∼ (nf-trans n n') (∞nf-trans s s')
  nf-trans (nunfold∼ z f) (nunfold∼ z' f') = nunfold∼ (nf-trans z z') (nf-trans f f')

  ne-trans : ∀{Γ σ} → {k l m : Ne Γ σ} → k Ne∼ l → l Ne∼ m → k Ne∼ m
  ne-trans (nvar∼ x) (nvar∼ x') = nvar∼ (trans x x')
  ne-trans (napp∼ t u) (napp∼ t' u') = napp∼ (ne-trans t t') (nf-trans u u')
  ne-trans (nfst∼ p) (nfst∼ q) = nfst∼ (ne-trans p q)
  ne-trans (nsnd∼ p) (nsnd∼ q) = nsnd∼ (ne-trans p q)
  ne-trans (nrec∼ z f n) (nrec∼ z' f' n') = nrec∼ (nf-trans z z') (nf-trans f f') (ne-trans n n')
  ne-trans (nhd∼ p) (nhd∼ q) = nhd∼ (ne-trans p q)
  ne-trans (ntl∼ p) (ntl∼ q) = ntl∼ (ne-trans p q)

  ∞nf-trans : ∀{Γ σ} → {k l m : ∞Nf<> Γ σ} → k ∞Nf∼ l → l ∞Nf∼ m → k ∞Nf∼ m
  ∼nforce (∞nf-trans p q) = nf-trans (∼nforce p) (∼nforce q)


≅toNf∼ : ∀{Γ σ} → {n n' : Nf Γ σ} → n ≅ n' → n Nf∼ n'
≅toNf∼ refl = nf-refl


postulate NfEq : ∀{Γ σ} → {n n' : Nf Γ σ} → n Nf∼ n' → n ≅ n'

mutual
  renNf : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Nf Δ σ → Nf Γ σ
  renNf α (nlam n) = nlam (renNf (wk α) n)
  renNf α (ne n) = ne (renNe α n)
  renNf α (a ,-, b) = renNf α a ,-, renNf α b
  renNf α nze = nze
  renNf α (nsu n) = nsu (renNf α n)
  renNf α (nstream h t) = nstream (renNf α h) (renNf∞ α t)
  renNf α (nunfold z f) = nunfold (renNf α z) (renNf α f)

  renNe : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Ne Δ σ → Ne Γ σ
  renNe α (nvar x) = nvar (α x)
  renNe α (napp t u) = napp (renNe α t) (renNf α u)
  renNe α (nfst n) = nfst (renNe α n)
  renNe α (nsnd n) = nsnd (renNe α n)
  renNe α (nrec z f n) = nrec (renNf α z) (renNf α f) (renNe α n)
  renNe α (nhd s) = nhd (renNe α s) 
  renNe α (ntl s) = ntl (renNe α s) 

  renNf∞ : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → ∞Nf<> Δ σ → ∞Nf<> Γ σ
  nforce (renNf∞ α n) = renNf α (nforce n) 


mutual
  rennecomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : Ne Γ σ) → renNe ρ' (renNe ρ v) Ne∼ renNe (ρ' ∘ ρ) v
  rennecomp ρ' ρ (nvar x) = nvar∼ refl
  rennecomp ρ' ρ (napp t u) = napp∼ (rennecomp ρ' ρ t) (rennfcomp ρ' ρ u)
  rennecomp ρ' ρ (nrec z f n) = nrec∼ (rennfcomp ρ' ρ z) (rennfcomp ρ' ρ f) (rennecomp ρ' ρ n)
  rennecomp ρ' ρ (nfst n) = nfst∼ (rennecomp ρ' ρ n)
  rennecomp ρ' ρ (nsnd n) = nsnd∼ (rennecomp ρ' ρ n)
  rennecomp ρ' ρ (nhd n) = nhd∼ (rennecomp ρ' ρ n)
  rennecomp ρ' ρ (ntl n) = ntl∼ (rennecomp ρ' ρ n)

  rennfcomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : Nf Γ σ) → renNf ρ' (renNf ρ v) Nf∼ renNf (ρ' ∘ ρ) v
  rennfcomp ρ' ρ (nlam v) = nlam∼ (nf-trans 
                                  (rennfcomp (wk ρ') (wk ρ) v) 
                                  (≅toNf∼ (cong (λ (f : Ren _ _) → renNf f v) (iext (λ _ → ext (λ x → sym (wkcomp ρ' ρ x)))))))  
  rennfcomp ρ' ρ (ne x) = ne∼ (rennecomp ρ' ρ x)
  rennfcomp ρ' ρ nze = nze∼
  rennfcomp ρ' ρ (nsu v) = nsu∼ (rennfcomp ρ' ρ v)
  rennfcomp ρ' ρ (a ,-, b) = rennfcomp ρ' ρ a ,∼, rennfcomp ρ' ρ b
  rennfcomp ρ' ρ (nstream h t) = nstream∼ (rennfcomp ρ' ρ h) (rennfcomp∞ ρ' ρ t)
  rennfcomp ρ' ρ (nunfold z f) = nunfold∼ (rennfcomp ρ' ρ z) (rennfcomp ρ' ρ f)
  
  rennfcomp∞ : ∀{Γ Δ E σ} → (ρ' : Ren Δ E)(ρ : Ren Γ Δ)(v : ∞Nf<> Γ σ) → renNf∞ ρ' (renNf∞ ρ v)  ∞Nf∼  renNf∞ (ρ' ∘ ρ) v
  ∼nforce (rennfcomp∞ ρ' ρ v) = rennfcomp ρ' ρ (nforce v)



mutual
  rennfid : ∀{Γ σ} → (n : Nf Γ σ) → renNf renId n Nf∼ n
  rennfid (nlam n) = nlam∼ (nf-trans 
                           (≅toNf∼ (cong (λ (f : Ren _ _) → (renNf f n)) (iext λ σ' → ext λ x → wkid x))) 
                           (rennfid n)) 
  rennfid (ne x) = ne∼ (renneid x)
  rennfid nze = nf-refl
  rennfid (nsu n) = nsu∼ (rennfid n)
  rennfid (a ,-, b) = rennfid a ,∼, rennfid b
  rennfid (nstream h t) = nstream∼ (rennfid h) (rennfid∞ t)
  rennfid (nunfold z f) = nunfold∼ (rennfid z) (rennfid f)
  
  renneid : ∀{Γ σ} → (n : Ne Γ σ) → renNe renId n Ne∼ n
  renneid (nvar x) = nvar∼ refl
  renneid (napp t u) = napp∼ (renneid t) (rennfid u)
  renneid (nrec z f n) = nrec∼ (rennfid z) (rennfid f) (renneid n)
  renneid (nfst n) = nfst∼ (renneid n)
  renneid (nsnd n) = nsnd∼ (renneid n)
  renneid (nhd n) = nhd∼ (renneid n)
  renneid (ntl n) = ntl∼ (renneid n)
  
  rennfid∞ : ∀{Γ σ} → (n : ∞Nf<> Γ σ) → renNf∞ renId n  ∞Nf∼  n
  ∼nforce (rennfid∞ n) = rennfid (nforce n)
 