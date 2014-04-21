{-# OPTIONS --copatterns #-}

module Values where

open import Syntax
open import NormalForms
open import Utils

open import Data.Nat hiding (_<_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Size


record Stream (A : Set) : Set where
  coinductive
  field shead : A
        stail : Stream A

open Stream public

record _S∼_ {A : Set}(s s' : Stream A) : Set where
  coinductive
  field hd∼ : shead s ≅ shead s'
        tl∼ : stail s S∼ stail s'
open _S∼_ public

postulate SEq : ∀{A} → {s s' : Stream A} → s S∼ s' → s ≅ s'


iso1 : ∀{A} → (s : Stream A) → (ℕ → A)
iso1 s zero = shead s
iso1 s (suc n) = iso1 (stail s) n

iso2 : ∀{A} → (ℕ → A) → Stream A
shead (iso2 f) = f zero
stail (iso2 f) = iso2 (λ n → f (suc n))

iso1iso2 : ∀{A} → (f : ℕ → A) → (n : ℕ) → iso1 (iso2 f) n ≅ f n
iso1iso2 f zero = refl
iso1iso2 f (suc n) = iso1iso2 (f ∘ suc) n  

iso2iso1 : ∀{A} → (s : Stream A) → iso2 (iso1 s) S∼ s
hd∼ (iso2iso1 s) = refl
tl∼ (iso2iso1 s) = iso2iso1 (stail s)

mutual
  Val : Con → Ty → Set
  Val Γ ι = Nf Γ ι
  Val Γ nat = Nf Γ nat
  Val Γ (σ ⇒ τ) = Σ (∀{Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ) 
                  λ f → ∀{Δ Δ'}(ρ : Ren Γ Δ)(ρ' : Ren Δ Δ')(v : Val Δ σ) → renval {σ = τ} ρ' (f ρ v) ≅ f (ρ' ∘ ρ) (renval {σ = σ} ρ' v)
  Val Γ (σ ∧ τ) = Val Γ σ × Val Γ τ
  Val Γ < σ > = Stream (Val Γ σ)

  renval : ∀{Γ Δ σ} → Ren Γ Δ → Val Γ σ → Val Δ σ
  renval {Γ} {Δ} {ι} α v   = renNf α v
  renval {Γ} {Δ} {nat} α v = renNf α v
  renval {Γ} {Δ} {σ ⇒ τ} α v = (λ {E} β v' → proj₁ v (renComp β α) v') , 
         (λ {Δ₁ Δ' : Con} (ρ : Ren Δ Δ₁) (ρ' : Ren Δ₁ Δ') (v₁ : Val Δ₁ σ) → 
           proof
           renval {σ = τ} ρ' (proj₁ v (λ {σ} x → ρ (α x)) v₁) 
           ≅⟨ proj₂ v {Δ₁} {Δ'} (renComp ρ α) ρ' v₁ ⟩
           proj₁ v (λ {σ} x → ρ' (ρ (α x))) (renval {σ = σ} ρ' v₁)
           ∎)
  renval {Γ} {Δ} {σ ∧ τ} α v = (renval {σ = σ} α (proj₁ v)) , (renval {σ = τ} α (proj₂ v))
  shead (renval {Γ} {Δ} {< σ >} α v) = renval {σ = σ} α (shead v)
  stail (renval {Γ} {Δ} {< σ >} α v) = renval {σ = < σ >} α (stail v)

renvalIso1 : ∀{Γ Δ σ} → (α : Ren Γ Δ)(s : Stream (Val Γ σ))(n : ℕ) → renval {σ = σ} α (iso1 s n) ≅ iso1 (renval {σ = < σ >} α s) n
renvalIso1 α s zero = refl
renvalIso1 {σ = σ} α s (suc n) = renvalIso1 {σ = σ} α (stail s) n

renvalIso2 : ∀{Γ Δ σ} → (f : ℕ → Val Γ σ) → (α : Ren Γ Δ) → renval {σ = < σ >} α (iso2 f) S∼ iso2 (λ n → renval {σ = σ} α (f n))
hd∼ (renvalIso2 f α) = refl
tl∼ (renvalIso2 f α) = renvalIso2 (λ n → f (suc n)) α


mutual
  renvalcomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E) → (ρ : Ren Γ Δ) → (v : Val Γ σ) → renval {σ = σ} ρ' (renval {σ = σ} ρ v) ≅ renval {σ = σ} (ρ' ∘ ρ) v 
  renvalcomp {σ = ι} ρ' ρ v = rennfcomp ρ' ρ v
  renvalcomp {σ = nat} ρ' ρ v = rennfcomp ρ' ρ v 
  renvalcomp {σ = σ ⇒ τ} ρ' ρ v = Σeq refl refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ₁ → ext λ ρ'' → ext λ v₁ → ir)
  renvalcomp {σ = σ ∧ τ} ρ' ρ v = cong₂ _,_ (renvalcomp {σ = σ} ρ' ρ (proj₁ v)) (renvalcomp {σ = τ} ρ' ρ (proj₂ v))
  renvalcomp {σ = < σ >} ρ' ρ v = SEq (∞renvalcomp ρ' ρ v)

  ∞renvalcomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E) → (ρ : Ren Γ Δ) → (v : Stream (Val Γ σ)) → renval {σ = < σ >} ρ' (renval {σ = < σ >} ρ v) S∼ renval {σ = < σ >} (ρ' ∘ ρ) v 
  hd∼ (∞renvalcomp {σ = σ} ρ' ρ v) = renvalcomp {σ = σ} ρ' ρ (shead v)
  tl∼ (∞renvalcomp {σ = σ} ρ' ρ v) = ∞renvalcomp ρ' ρ (stail v)

mutual
  renvalid : ∀{Γ σ} → (v : Val Γ σ) → renval {σ = σ} renId v ≅ v
  renvalid {Γ} {ι}   v = rennfid v
  renvalid {Γ} {nat} v = rennfid v
  renvalid {Γ} {σ ⇒ τ} v = Σeq (iext λ E → ext λ a → refl) refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ → ext λ ρ' → ext λ v₁ → fixedtypesright refl)
  renvalid {σ = σ ∧ τ} (a , b) = cong₂ _,_ (renvalid {σ = σ} a) (renvalid {σ = τ} b)
  renvalid {σ = < σ >} s = SEq (∞renvalid s) 

  ∞renvalid : ∀{Γ σ} → (v : Val Γ < σ >) → renval {σ = < σ >} renId v S∼ v
  hd∼ (∞renvalid {σ = σ} v) = renvalid {σ = σ} (shead v)
  tl∼ (∞renvalid v) = ∞renvalid (stail v)


Env : Con → Con → Set
Env Γ Δ = ∀{σ} → Var Γ σ → Val Δ σ


_<<_ : ∀{Γ Δ} → Env Γ Δ → ∀{σ} → Val Δ σ → Env (Γ < σ) Δ
(γ << v) vze = v
(γ << v) (vsu x) = γ x 


renval<< : ∀{Γ Δ E σ} → (ρ : Ren Δ E) → (γ : Env Γ Δ) → (v : Val Δ σ) → ∀{τ}(x : Var (Γ < σ) τ) → 
         (renval {σ = τ} ρ ∘ (γ << v)) x ≅ ((λ {σ'} → renval {σ = σ'} ρ ∘ γ) << renval {σ = σ} ρ v) x
renval<< ρ γ v vze = refl
renval<< ρ γ v (vsu x) = refl
