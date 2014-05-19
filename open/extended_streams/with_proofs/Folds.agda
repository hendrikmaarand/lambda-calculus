module Folds where

open import Syntax
open import NormalForms
open import Values
open import ReifyReflect

open import Data.Product hiding (map)
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)



natfold : ∀{Γ σ} → Val Γ σ  → Val Γ (σ ⇒ σ) → Val Γ nat → Val Γ σ
natfold {σ = σ} z f (nenat x) = reflect σ (nrec (reify _ z) (reify _ f) x)
natfold z f nze = z
natfold {σ = σ} z f (nsu n) = proj₁ f renId (natfold {σ = σ} z f n)



renvalnatfold : ∀{Γ Δ σ} (ρ : Ren Γ Δ)(z : Val Γ σ)(f : Val Γ (σ ⇒ σ))(n : Val Γ nat) → renval {σ = σ} ρ (natfold {σ = σ} z f n) ≅ 
              natfold {σ = σ} (renval {σ = σ} ρ z) (renval {σ = σ ⇒ σ} ρ f) (renval {σ = nat} ρ n)
renvalnatfold {σ = σ}ρ z f (nenat x) = proof
  renval {σ = σ} ρ (reflect σ (nrec (reify σ z) (nlam (reify σ (proj₁ f vsu (reflect σ (nvar vze))))) x))
  ≅⟨ renvalReflect ρ ((nrec (reify σ z) (nlam (reify σ (proj₁ f vsu (reflect σ (nvar vze))))) x)) ⟩
  reflect σ (renNe ρ (nrec (reify σ z) (nlam (reify σ (proj₁ f vsu (reflect σ (nvar vze))))) x))
  ≅⟨ cong (reflect σ) (cong₃ nrec 
    (reifyRenval ρ z) 
    (cong nlam (proof
          renNf (wk ρ) (reify σ (proj₁ f vsu (reflect σ (nvar vze))))
          ≅⟨ reifyRenval (wk ρ) (proj₁ f vsu (reflect σ (nvar vze))) ⟩
          reify σ (renval {σ = σ} (wk ρ) (proj₁ f vsu (reflect σ (nvar vze))))
          ≅⟨ cong (reify σ) (proj₂ f vsu (wk ρ) (reflect σ (nvar vze))) ⟩
          reify σ (proj₁ f ((wk ρ) ∘ vsu) (renval {σ = σ} (wk ρ) (reflect σ (nvar vze))))
          ≅⟨ cong (reify σ) (cong₂ (proj₁ f) refl (renvalReflect {σ = σ} (wk ρ) (nvar vze))) ⟩
          reify σ (proj₁ f (vsu ∘ ρ) (reflect σ (nvar vze)))
          ∎)) 
    (proof renNe ρ x ≡⟨⟩ renNe ρ x ∎)) ⟩
  reflect σ (nrec (reify σ (renval {σ = σ} ρ z)) (nlam (reify σ (proj₁ f (vsu ∘ ρ) (reflect σ (nvar vze))))) (renNe ρ x))
  ∎
renvalnatfold {σ = σ} ρ z f nze = proof renval {σ = σ} ρ z ≡⟨⟩ renval {σ = σ} ρ z ∎
renvalnatfold {σ = σ} ρ z f (nsu n) = proof
  renval {σ = σ} ρ (proj₁ f renId (natfold {σ = σ} z f n)) 
  ≅⟨ proj₂ f renId ρ (natfold {σ = σ} z f n) ⟩
  proj₁ f ρ (renval {σ = σ} ρ (natfold {σ = σ} z f n))
  ≅⟨ cong (proj₁ f ρ) (renvalnatfold {σ = σ} ρ z f n) ⟩
  proj₁ f ρ (natfold {σ = σ} (renval {σ = σ} ρ z) ((λ β → proj₁ f (β ∘ ρ)) , (λ ρ₁ ρ' v₁ → trans (proj₂ f (ρ₁ ∘ ρ) ρ' v₁) refl)) (renNf ρ n))
  ∎


renvalinner : ∀{Γ Δ σ τ} → (f : Val Γ (σ ⇒ τ ⇒ τ))(α : Ren Γ Δ)(x : Val Γ σ)(y : Val Δ τ) → 
            proj₁ (proj₁ f renId x) α y ≅ proj₁ (proj₁ f α (renval {σ = σ} α x)) renId y
renvalinner {Γ}{Δ}{σ = σ}{τ = τ} f α x y = proof
  proj₁ (proj₁ f renId x) α y 
  ≡⟨⟩
  proj₁ (renval {σ = τ ⇒ τ} α (proj₁ f renId x)) renId y
  ≅⟨ cong (λ (f : Val Δ (τ ⇒ τ)) → proj₁ f renId y) (proj₂ f renId α x) ⟩
  proj₁ (proj₁ f α (renval {σ = σ} α x)) renId y
  ∎ 
