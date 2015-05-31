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


mutual
  record Stream (Γ : Con) (σ : Ty) : Set where
    constructor St
    field x : Val Γ σ
          f : Val Γ (σ ⇒ σ)
  
  Val : Con → Ty → Set
  Val Γ ι = Nf Γ ι
  Val Γ nat = Nf Γ nat
  Val Γ (σ ⇒ τ) = Σ (∀{Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ) 
                  λ f → ∀{Δ Δ'}(ρ : Ren Γ Δ)(ρ' : Ren Δ Δ')(v : Val Δ σ) → renval {σ = τ} ρ' (f ρ v) ≅ f (ρ' ∘ ρ) (renval {σ = σ} ρ' v)
  Val Γ (σ ∧ τ) = Val Γ σ × Val Γ τ
  Val Γ < σ > = Stream Γ σ

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
  renval {Γ} {Δ} {< σ >} α v = record { 
    x = renval {σ = σ} α (Stream.x v) ; 
    f = (λ {E} α' v' → proj₁ (Stream.f v) (renComp α' α) v') , 
        (λ {Δ₁ Δ' : Con} ρ ρ' v₁ → 
          proof
          renval {σ = σ} ρ' (proj₁ (Stream.f v) (renComp ρ α) v₁)
          ≅⟨ proj₂ (Stream.f v) (renComp ρ α) ρ' v₁ ⟩
          proj₁ (Stream.f v) (renComp (ρ' ∘ ρ) α) (renval {σ = σ} ρ' v₁)
          ∎) }

open Stream public

SEq : ∀{Γ σ} → {xx xx' : Val Γ σ} → {ff ff' : Val Γ (σ ⇒ σ)} → (p : xx ≅ xx') → (q : ff ≅ ff') → St {Γ} {σ} xx ff ≅ St {Γ} {σ} xx' ff'
SEq {Γ} {σ} p q = funny p q (λ x f → St x f)


renvalcomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E) → (ρ : Ren Γ Δ) → (v : Val Γ σ) → renval {σ = σ} ρ' (renval {σ = σ} ρ v) ≅ renval {σ = σ} (ρ' ∘ ρ) v 
renvalcomp {σ = ι} ρ' ρ v = rennfcomp ρ' ρ v
renvalcomp {σ = nat} ρ' ρ v = rennfcomp ρ' ρ v 
renvalcomp {σ = σ ⇒ τ} ρ' ρ v = Σeq refl refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ₁ → ext λ ρ'' → ext λ v₁ → ir)
renvalcomp {σ = σ ∧ τ} ρ' ρ v = cong₂ _,_ (renvalcomp {σ = σ} ρ' ρ (proj₁ v)) (renvalcomp {σ = τ} ρ' ρ (proj₂ v))
renvalcomp {σ = < σ >} ρ' ρ (St x f) = SEq (renvalcomp {σ = σ} ρ' ρ x) ((Σeq refl refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ₁ → ext λ ρ'' → ext λ v₁ → ir)))

renvalid : ∀{Γ σ} → (v : Val Γ σ) → renval {σ = σ} renId v ≅ v
renvalid {Γ} {ι}   v = rennfid v
renvalid {Γ} {nat} v = rennfid v
renvalid {Γ} {σ ⇒ τ} v = Σeq refl refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ → ext λ ρ' → ext λ v₁ → fixedtypesright refl)
renvalid {σ = σ ∧ τ} (a , b) = cong₂ _,_ (renvalid {σ = σ} a) (renvalid {σ = τ} b)
renvalid {Γ} {σ = < σ >} (St x f) = SEq {Γ} {σ} 
  (renvalid {σ = σ} x) 
  (Σeq refl refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ → ext λ ρ' → ext λ v₁ → fixedtypesright refl))


Env : Con → Con → Set
Env Γ Δ = ∀{σ} → Var Γ σ → Val Δ σ


_<<_ : ∀{Γ Δ} → Env Γ Δ → ∀{σ} → Val Δ σ → Env (Γ < σ) Δ
(γ << v) vze = v
(γ << v) (vsu x) = γ x 


renval<< : ∀{Γ Δ E σ} → (ρ : Ren Δ E) → (γ : Env Γ Δ) → (v : Val Δ σ) → ∀{τ}(x : Var (Γ < σ) τ) → 
         (renval {σ = τ} ρ ∘ (γ << v)) x ≅ ((λ {σ'} → renval {σ = σ'} ρ ∘ γ) << renval {σ = σ} ρ v) x
renval<< ρ γ v vze = refl
renval<< ρ γ v (vsu x) = refl

renenv : ∀{Γ Δ E} → Ren Δ E → Env Γ Δ → Env Γ E
renenv {ε} α γ ()
renenv {Γ < σ} α γ vze = renval {σ = σ} α (γ vze)
renenv {Γ < σ} α γ (vsu x) = renenv α (γ ∘ vsu) x 

