{-# OPTIONS --copatterns #-}

module Folds where

open import Syntax
open import NormalForms
open import Values

--open import Data.Nat hiding (_<_)
open import Data.Product hiding (map)
--open import Data.Sum hiding (map)
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
--open import Size


{-
natfold : ∀{Γ σ} → Val Γ σ  → Val Γ (σ ⇒ σ) → Val Γ nat → Val Γ σ
natfold {σ = σ} z f (ne x) = reflect σ (nrec (reify _ z) (reify _ f) x)
natfold z f nze = z
natfold {σ = σ} z f (nsu n) = proj₁ f renId (natfold {σ = σ} z f n)
-}

head : ∀{Γ σ} → StreamVal (Val Γ σ) (Ne Γ < σ >) → Val Γ σ
head (neSV x) = {!!}
head (streamSV h t) = h


tail : ∀{Γ σ} → StreamVal (Val Γ σ) (Ne Γ < σ >) → Val Γ < σ >
tail (neSV x) = {!!}
tail (streamSV h t) = vforce t


mutual
  unFold : ∀{Γ σ τ} → (z : Val Γ σ) → (f : Val Γ (σ ⇒ σ ∧ τ)) → StreamVal (Val Γ τ) (Ne Γ < τ >)
  unFold {σ = σ} z f = let z' , v = proj₁ f renId z in streamSV v (∞unFold {σ = σ} z' f)

  ∞unFold : ∀{Γ σ τ} → (z : Val Γ σ) → (f : Val Γ (σ ⇒ σ ∧ τ)) → ∞StreamVal (Val Γ τ) (Ne Γ < τ >)
  vforce (∞unFold {σ = σ} z f) = unFold {σ = σ} z f

{-
listfold : ∀{Γ σ τ} → Val Γ τ → Val Γ (σ ⇒ τ ⇒ τ) → Val Γ [ σ ] → Val Γ τ
listfold {σ = σ}{τ = τ} z f (neLV x) = reflect τ (nfold {σ = σ}{τ = τ} (reify _ z) (reify _ f) x)
listfold z f nilLV = z
listfold {τ = τ} z f (consLV x xs) = proj₁ (proj₁ f renId x) renId (listfold {τ = τ} z f xs)


renvalnatfold : ∀{Γ Δ σ} (ρ : Ren Γ Δ)(z : Val Γ σ)(f : Val Γ (σ ⇒ σ))(n : Val Γ nat) → renval {σ = σ} ρ (natfold {σ = σ} z f n) ≅ 
              natfold {σ = σ} (renval {σ = σ} ρ z) (renval {σ = σ ⇒ σ} ρ f) (renval {σ = nat} ρ n)
renvalnatfold {σ = σ}ρ z f (nenat x) = proof
  renval {σ = σ} ρ (reflect σ (nrec (reify σ z) (nlam (reify σ (proj₁ f suc (reflect σ (nvar zero))))) x))
  ≅⟨ renvalReflect ρ ((nrec (reify σ z) (nlam (reify σ (proj₁ f suc (reflect σ (nvar zero))))) x)) ⟩
  reflect σ (renNe ρ (nrec (reify σ z) (nlam (reify σ (proj₁ f suc (reflect σ (nvar zero))))) x))
  ≅⟨ cong (reflect σ) (cong₃ nrec 
    (reifyRenval ρ z) 
    (cong nlam (proof
          renNf (wk ρ) (reify σ (proj₁ f suc (reflect σ (nvar zero))))
          ≅⟨ reifyRenval (wk ρ) (proj₁ f suc (reflect σ (nvar zero))) ⟩
          reify σ (renval {σ = σ} (wk ρ) (proj₁ f suc (reflect σ (nvar zero))))
          ≅⟨ cong (reify σ) (proj₂ f suc (wk ρ) (reflect σ (nvar zero))) ⟩
          reify σ (proj₁ f ((wk ρ) ∘ suc) (renval {σ = σ} (wk ρ) (reflect σ (nvar zero))))
          ≅⟨ cong (reify σ) (cong₂ (proj₁ f) refl (renvalReflect {σ = σ} (wk ρ) (nvar zero))) ⟩
          reify σ (proj₁ f (suc ∘ ρ) (reflect σ (nvar zero)))
          ∎)) 
    (proof renNe ρ x ≡⟨⟩ renNe ρ x ∎)) ⟩
  reflect σ (nrec (reify σ (renval {σ = σ} ρ z)) (nlam (reify σ (proj₁ f (suc ∘ ρ) (reflect σ (nvar zero))))) (renNe ρ x))
  ∎
renvalnatfold {σ = σ} ρ z f nzero = proof renval {σ = σ} ρ z ≡⟨⟩ renval {σ = σ} ρ z ∎
renvalnatfold {σ = σ} ρ z f (nsuc n) = proof
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


renvallistfold : ∀{Γ Δ σ τ} (ρ : Ren Γ Δ)(z : Val Γ τ)(f : Val Γ (σ ⇒ τ ⇒ τ))(n : Val Γ [ σ ]) → renval {σ = τ} ρ (listfold {τ = τ} z f n) ≅ 
              listfold {τ = τ} (renval {σ = τ} ρ z) (renval {σ = σ ⇒ τ ⇒ τ} ρ f) (renval {σ = [ σ ]} ρ n)
renvallistfold {σ = σ}{τ = τ} ρ z f (neLV x) = proof
  renval {σ = τ} ρ (reflect τ (nfold (reify τ z) (nlam (nlam (reify τ (proj₁ (proj₁ f suc (reflect σ (nvar zero))) suc (reflect τ (nvar zero)))))) x))
  ≅⟨ renvalReflect ρ (nfold (reify τ z) (nlam (nlam (reify τ (proj₁ (proj₁ f suc (reflect σ (nvar zero))) suc (reflect τ (nvar zero)))))) x) ⟩
  reflect τ (renNe ρ (nfold (reify τ z) (nlam (nlam (reify τ (proj₁ (proj₁ f suc (reflect σ (nvar zero))) suc (reflect τ (nvar zero)))))) x))
  ≅⟨ cong (reflect τ) 
     (cong₃ nfold 
       (reifyRenval ρ z) --reify τ (proj₁ (renval {σ = τ ⇒ τ} (wk ρ) (proj₁ f suc (reflect σ (nvar zero)))) suc (reflect τ (nvar zero)))
       (cong (λ x → nlam (nlam x)) (proof
         renNf (wk (wk ρ)) (reify τ (proj₁ (proj₁ f suc (reflect σ (nvar zero))) suc (reflect τ (nvar zero))))
         ≅⟨ reifyRenval (wk (wk ρ)) (proj₁ (proj₁ f suc (reflect σ (nvar zero))) suc (reflect τ (nvar zero))) ⟩
         reify τ (renval {σ = τ} (wk (wk ρ)) (proj₁ (proj₁ f suc (reflect σ (nvar zero))) suc (reflect τ (nvar zero))))
         ≅⟨ cong (reify τ) (proj₂ (proj₁ f suc (reflect σ (nvar zero))) suc (wk (wk ρ)) (reflect τ (nvar zero)) ) ⟩
         reify τ (proj₁ (proj₁ f suc (reflect σ (nvar zero))) (renComp suc (wk ρ)) (renval {σ = τ} (wk (wk ρ)) (reflect τ (nvar zero))))
         ≅⟨ cong (λ x → reify τ (proj₁ (proj₁ f suc (reflect σ (nvar zero))) (renComp suc (wk ρ)) x)) (renvalReflect (wk (wk ρ)) (nvar zero)) ⟩
         reify τ (proj₁ (proj₁ f suc (reflect σ (nvar zero))) (renComp suc (wk ρ)) (reflect τ (nvar zero)))
         ≡⟨⟩
         reify τ (proj₁ (renval {σ = τ ⇒ τ} (wk ρ) (proj₁ f suc (reflect σ (nvar zero)))) suc (reflect τ (nvar zero)))
         ≅⟨ cong (λ (f : Val _ (τ ⇒ τ)) → reify τ (proj₁ f suc (reflect τ (nvar zero)))) (proj₂ f suc (wk ρ) (reflect σ (nvar zero))) ⟩
         reify τ (proj₁ (proj₁ f (renComp (wk ρ) suc) (renval {σ = σ} (wk ρ) (reflect σ (nvar zero)))) suc (reflect τ (nvar zero)))
         ≅⟨ cong (λ x → reify τ (proj₁ (proj₁ f (renComp (wk ρ) suc) x) suc (reflect τ (nvar zero)))) (renvalReflect (wk ρ) (nvar zero)) ⟩
         reify τ (proj₁ (proj₁ f (renComp (wk ρ) suc) (reflect σ (nvar zero))) suc (reflect τ (nvar zero)))
         ≡⟨⟩
         reify τ (proj₁ (proj₁ f (renComp suc ρ) (reflect σ (nvar zero))) suc (reflect τ (nvar zero)))
         ∎)) 
       refl) ⟩
  reflect τ (nfold (reify τ (renval {σ = τ} ρ z)) (nlam (nlam (reify τ (proj₁ (proj₁ f (renComp suc ρ) (reflect σ (nvar zero))) suc (reflect τ (nvar zero)))))) (renNe ρ x))
  ∎
renvallistfold ρ z f nilLV = refl
renvallistfold {σ = σ}{τ = τ} ρ z f (consLV x xs) = proof
  renval {σ = τ} ρ (proj₁ (proj₁ f renId x) renId (listfold {τ = τ} z f xs)) 
  ≅⟨ proj₂ (proj₁ f renId x) renId ρ (listfold {τ = τ} z f xs) ⟩ 
  proj₁ (proj₁ f renId x) ρ (renval {σ = τ} ρ (listfold {τ = τ} z f xs))
  ≅⟨ cong (proj₁ (proj₁ f renId x) ρ) (renvallistfold {σ = σ}{τ = τ} ρ z f xs) ⟩
  proj₁ (proj₁ f renId x) ρ (listfold {τ = τ} (renval {σ = τ} ρ z) ((λ {E} β → proj₁ f (renComp β ρ)) ,
       (λ {Δ₁} {Δ'} ρ₁ ρ' v₁ → trans (proj₂ f (renComp ρ₁ ρ) ρ' v₁) refl)) (mapLV (renval {σ = σ} ρ) (renNe ρ) xs))
  ≅⟨ renvalinner {σ = σ}{τ = τ} f ρ x ((listfold {τ = τ} (renval {σ = τ} ρ z) ((λ {E} β → proj₁ f (renComp β ρ)) ,
       (λ {Δ₁} {Δ'} ρ₁ ρ' v₁ → trans (proj₂ f (renComp ρ₁ ρ) ρ' v₁) refl)) (mapLV (renval {σ = σ} ρ) (renNe ρ) xs))) ⟩
  proj₁ (proj₁ f (renComp renId ρ) (renval {σ = σ} ρ x)) renId 
    (listfold {τ = τ} (renval {σ = τ} ρ z) ((λ {E} β → proj₁ f (renComp β ρ)) , 
    (λ {Δ₁} {Δ'} ρ₁ ρ' v₁ → trans (proj₂ f (renComp ρ₁ ρ) ρ' v₁) refl)) (mapLV (renval {σ = σ} ρ) (renNe ρ) xs))
  ∎

-}