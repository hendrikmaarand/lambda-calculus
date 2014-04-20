{-# OPTIONS --copatterns #-}

module ReifyReflect where

open import Syntax
open import NormalForms
open import Values
open import Utils

open import Data.Nat hiding (_<_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Size


mutual
  reify : ∀{Γ} σ → Val Γ σ → Nf Γ σ
  reify ι   v = v
  reify nat v = v
  reify (σ ⇒ τ) v = nlam (reify τ (proj₁ v vsu (reflect σ (nvar vze))))
  reify (σ ∧ τ) v = reify σ (proj₁ v) ,-, reify τ (proj₂ v)
  reify < σ > v = ntup (λ n → reify σ (iso1 v n))
  
  reflect : ∀{Γ} σ → Ne Γ σ → Val Γ σ
  reflect ι   n = ne n
  reflect nat n = ne n
  reflect (σ ⇒ τ) n = (λ α v → reflect τ (napp (renNe α n) (reify σ v))) , (λ ρ ρ' v → 
    proof
    renval {σ = τ} ρ' (reflect τ (napp (renNe ρ n) (reify σ v)))
    ≅⟨ renvalReflect {σ = τ} ρ' (napp (renNe ρ n) (reify σ v)) ⟩
    reflect τ (renNe ρ' (napp (renNe ρ n) (reify σ v)))
    ≅⟨ cong (reflect τ) refl ⟩
    reflect τ (napp (renNe ρ' (renNe ρ n)) (renNf ρ' (reify σ v)))
    ≅⟨ cong (reflect τ) (cong₂ napp (rennecomp ρ' ρ n) (reifyRenval ρ' v)) ⟩
    reflect τ (napp (renNe (ρ' ∘ ρ) n) (reify σ (renval {σ = σ} ρ' v)))
    ∎)
  reflect (σ ∧ τ) n = (reflect σ (nfst n)) , (reflect τ (nsnd n))
  reflect < σ > n = iso2 (λ a → reflect σ (nproj a n))


  renvalReflect : ∀{Γ Δ σ}(ρ : Ren Γ Δ)(n : Ne Γ σ) → renval {σ = σ} ρ (reflect σ n) ≅ reflect σ (renNe ρ n)
  renvalReflect {Γ} {Δ} {ι} ρ n = refl
  renvalReflect {Γ} {Δ} {nat} ρ n = cong ne refl
  renvalReflect {Γ} {Δ} {σ ⇒ τ} ρ n = Σeq 
    (iext λ _ → ext λ (α : Ren _ _) → ext λ v → proof
      reflect τ (napp (renNe (α ∘ ρ) n) (reify σ v))
      ≅⟨ cong (reflect τ) (cong₂ napp (sym (rennecomp α ρ n)) refl) ⟩ 
      reflect τ (napp (renNe α (renNe ρ n)) (reify σ v))
      ∎) 
    refl
    ((iext λ _ → iext λ _ → ext λ (ρ₁ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v₁ → fixedtypes (proof
      reflect τ (napp (renNe (ρ' ∘ ρ₁ ∘ ρ) n) (reify σ (renval {σ = σ} ρ' v₁)))
      ≅⟨ cong (reflect τ) (cong₂ napp (sym (rennecomp ρ' (ρ₁ ∘ ρ) n)) (sym (reifyRenval ρ' v₁))) ⟩
      reflect τ (napp (renNe ρ' (renNe (ρ₁ ∘ ρ) n)) (renNf ρ' (reify σ v₁)))
      ≅⟨ cong (reflect τ) (cong₂ napp refl refl) ⟩
      reflect τ (renNe ρ' (napp (renNe (ρ₁ ∘ ρ) n) (reify σ v₁)))
      ≅⟨ sym (renvalReflect ρ' (napp (renNe (ρ₁ ∘ ρ) n) (reify σ v₁))) ⟩
      renval {σ = τ} ρ' (reflect τ (napp (renNe (ρ₁ ∘ ρ) n) (reify σ v₁)))
      ≅⟨ cong ( λ f → renval {σ = τ} ρ' (reflect τ (napp f (reify σ v₁)))) (sym (rennecomp ρ₁ ρ n)) ⟩
      renval {σ = τ} ρ' (reflect τ (napp (renNe ρ₁ (renNe ρ n)) (reify σ v₁)))
      ∎)))
  renvalReflect {Γ} {Δ} {σ ∧ τ} ρ n = cong₂ _,_ (renvalReflect ρ (nfst n)) (renvalReflect ρ (nsnd n))
  renvalReflect {Γ} {Δ} {< σ >} ρ n = {!!}

{-
    proof
    renval {σ = < σ >} ρ (iso2 (λ a → reflect σ (nproj a n))) 
    ≅⟨ {!!} ⟩
    iso2 (λ a → reflect σ (nproj a (renNe ρ n)))
    ∎ --SEq (renvalIso2 ρ n)
-}


  renvalIso2 : ∀{Γ Δ σ} → (α : Ren Γ Δ)(n : Ne Γ < σ >) → 
             renval {σ = < σ >} α (iso2 (λ a → reflect σ (nproj a n))) S∼ iso2 (λ a → reflect σ (nproj a (renNe α n)))
  hd∼ (renvalIso2 α n) = renvalReflect α (nproj zero n)
  tl∼ (renvalIso2 α n) = {!iso2 ?!}


  reifyRenval : ∀{Γ Δ σ}(ρ : Ren Γ Δ)(n : Val Γ σ) → renNf ρ (reify σ n) ≅ reify σ (renval {σ = σ} ρ n)
  reifyRenval {Γ} {Δ} {ι}   ρ n = proof renNf ρ n ≡⟨⟩ renNf ρ n ∎
  reifyRenval {σ = nat} ρ v = refl
  reifyRenval {Γ} {Δ} {σ ⇒ τ} ρ n = proof
    nlam (renNf (wk ρ) (reify τ (proj₁ n vsu (reflect σ (nvar vze)))))
    ≅⟨ cong nlam (reifyRenval (wk ρ) (proj₁ n vsu (reflect σ (nvar vze)))) ⟩
    nlam (reify τ (renval {σ = τ} (wk ρ) (proj₁ n vsu (reflect σ (nvar vze)))))
    ≅⟨ cong nlam (cong (reify τ) (proj₂ n vsu (wk ρ) (reflect σ (nvar vze)))) ⟩
    nlam (reify τ (proj₁ n ((wk ρ) ∘ vsu) (renval {σ = σ} (wk ρ) (reflect σ (nvar vze)))))
    ≅⟨ cong nlam (cong (reify τ) (cong₂ (proj₁ n) refl (renvalReflect {σ = σ} (wk ρ) (nvar vze)))) ⟩
    nlam (reify τ (proj₁ n (vsu ∘ ρ) (reflect σ (nvar vze))))
    ∎
  reifyRenval {σ = σ ∧ τ} ρ v = cong₂ _,-,_ (reifyRenval ρ (proj₁ v)) (reifyRenval ρ (proj₂ v))
  reifyRenval {σ = < σ >} ρ s = cong ntup (ext (λ n → trans (reifyRenval {σ = σ} ρ (iso1 s n)) (cong (reify σ) (renvalIso1 ρ s n))))

