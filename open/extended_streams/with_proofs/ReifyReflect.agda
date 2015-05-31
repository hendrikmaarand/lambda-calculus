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
  reify < σ > (St x f) = nunf (reify σ x) (nlam (reify σ (proj₁ f vsu (reflect σ (nvar vze)))))
  
  reflect : ∀{Γ} σ → Ne Γ σ → Val Γ σ
  reflect ι   n = ne n
  reflect nat n = nenat n
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
  reflect < σ > n = St (reflect σ (nsh n)) ((λ α v → reflect σ (nsh (nst (renNe α n)))) , (λ ρ ρ' v → 
    proof
    renval {σ = σ} ρ' (reflect σ (nsh (nst (renNe ρ n)))) 
    ≅⟨ renvalReflect ρ' (nsh (nst (renNe ρ n))) ⟩
    reflect σ (nsh (nst (renNe ρ' (renNe ρ n))))
    ≅⟨ cong (λ t → reflect σ (nsh (nst t))) (rennecomp ρ' ρ n) ⟩
    reflect σ (nsh (nst (renNe (ρ' ∘ ρ) n)))
    ∎))


  renvalReflect : ∀{Γ Δ σ}(ρ : Ren Γ Δ)(n : Ne Γ σ) → renval {σ = σ} ρ (reflect σ n) ≅ reflect σ (renNe ρ n)
  renvalReflect {Γ} {Δ} {ι} ρ n = refl
  renvalReflect {Γ} {Δ} {nat} ρ n = cong nenat refl
  renvalReflect {Γ} {Δ} {σ ⇒ τ} ρ n = Σeq 
    (iext λ _ → ext λ (α : Ren _ _) → ext λ v → proof
      reflect τ (napp (renNe (α ∘ ρ) n) (reify σ v))
      ≅⟨ cong (reflect τ) (cong₂ napp (sym (rennecomp α ρ n)) refl) ⟩ 
      reflect τ (napp (renNe α (renNe ρ n)) (reify σ v))
      ∎) 
    refl
    ((iext λ _ → iext λ _ → ext λ (ρ₁ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v₁ → fixedtypesright (
      cong (λ t → reflect τ (napp t (reify σ (renval {σ = σ} ρ' v₁)))) (sym (rennecomp (ρ' ∘ ρ₁) ρ n)))))
  renvalReflect {Γ} {Δ} {σ ∧ τ} ρ n = cong₂ _,_ (renvalReflect ρ (nfst n)) (renvalReflect ρ (nsnd n))
  renvalReflect {Γ} {Δ} {< σ >} ρ n = SEq (renvalReflect ρ (nsh n)) 
    (Σeq (iext λ _ → ext λ (α : Ren _ _) → ext λ v → cong (λ t → reflect σ (nsh (nst t))) (sym (rennecomp α ρ n)) ) 
         refl 
         (iext λ _ → iext λ _ → ext λ (ρ₁ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v₁ → fixedtypesright (
           cong (λ t → reflect σ (nsh (nst t))) (sym (rennecomp (ρ' ∘ ρ₁) ρ n)))))


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
  reifyRenval {σ = < σ >} ρ s = cong₂ nunf (reifyRenval ρ (x s)) (proof
    nlam (renNf (wk ρ) (reify σ (proj₁ (f s) vsu (reflect σ (nvar vze)))))
    ≅⟨ cong nlam (reifyRenval (wk ρ) (proj₁ (f s) vsu (reflect σ (nvar vze)))) ⟩
    nlam (reify σ (renval {σ = σ} (wk ρ) (proj₁ (f s) vsu (reflect σ (nvar vze)))))
    ≅⟨ cong (λ t → nlam (reify σ t)) (proj₂ (f s) vsu (wk ρ) (reflect σ (nvar vze))) ⟩
    nlam (reify σ (proj₁ (f s) ((wk ρ) ∘ vsu) (renval {σ = σ} (wk ρ) (reflect σ (nvar vze)))))
    ≅⟨ cong nlam (cong (reify σ) (cong₂ (proj₁ (f s)) refl (renvalReflect {σ = σ} (wk ρ) (nvar vze)))) ⟩
    nlam (reify σ (proj₁ (f s) (renComp vsu ρ) (reflect σ (nvar vze))))
    ∎)

