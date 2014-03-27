{-# OPTIONS --copatterns --termination-depth=1 #-}


module Norm where

open import Syntax
open import NormalForms
open import Values
open import ReifyReflect
open import Evaluator
open import Folds
open import Utils

open import Function
open import Data.Product hiding (map)
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Size



data _∼_ : ∀{Γ}{σ} → Tm Γ σ → Tm Γ σ → Set where
  refl∼  : ∀{Γ}{σ} → {t : Tm Γ σ} → t ∼ t
  sym∼   : ∀{Γ}{σ} → {t u : Tm Γ σ} → t ∼ u → u ∼ t
  trans∼ : ∀{Γ}{σ} → {t u v : Tm Γ σ} → t ∼ u → u ∼ v → t ∼ v
  beta∼  : ∀{Γ σ τ} → {t : Tm (Γ < σ) τ} → {u : Tm Γ σ} → app (lam t) u ∼ sub (sub<< var u) t
  eta∼   : ∀{Γ σ τ} → {t : Tm Γ (σ ⇒ τ)} → t ∼ lam (app (ren vsu t) (var vze))
  congapp∼  : ∀{Γ σ τ} → {t t' : Tm Γ (σ ⇒ τ)} → {u u' : Tm Γ σ} → t ∼ t' → u ∼ u' → app t u ∼ app t' u'
  conglam∼  : ∀{Γ σ τ} → {t t' : Tm (Γ < σ) τ} → t ∼ t' → lam t ∼ lam t'
  congsc∼   : ∀{Γ} → {t t' : Tm Γ nat} → t ∼ t' → su t ∼ su t'
  congrec∼  : ∀{Γ σ} → {z z' : Tm Γ σ}{f f' : Tm Γ (σ ⇒ σ)}{n n' : Tm Γ nat} → z ∼ z' → f ∼ f' → n ∼ n' → rec z f n ∼ rec z' f' n'
  congreczero∼ : ∀{Γ σ} → (z : Tm Γ σ)(f : Tm Γ (σ ⇒ σ)) → rec z f ze ∼ z
  congrecsc∼   : ∀{Γ σ} → (z : Tm Γ σ)(f : Tm Γ (σ ⇒ σ))(n : Tm Γ nat) → rec z f (su n) ∼ app f (rec z f n)
  congpair∼    : ∀{Γ σ τ} → {a a' : Tm Γ σ}{b b' : Tm Γ τ} → a ∼ a' → b ∼ b' → (a ,, b) ∼ (a' ,, b')
  congfst∼     : ∀{Γ σ τ} → {a a' : Tm Γ (σ ∧ τ)} → a ∼ a' → fst a ∼ fst a'
  congsnd∼     : ∀{Γ σ τ} → {a a' : Tm Γ (σ ∧ τ)} → a ∼ a' → snd a ∼ snd a'
  congunfold∼  : ∀{Γ σ τ} → {z z' : Tm Γ σ}{f f' : Tm Γ (σ ⇒ σ ∧ τ)} → z ∼ z' → f ∼ f' → unfold z f ∼ unfold z' f'
  conghd∼  : ∀{Γ σ} → {s s' : Tm Γ < σ >} → s ∼ s' → hd s ∼ hd s'
  congtl∼  : ∀{Γ σ} → {s s' : Tm Γ < σ >} → s ∼ s' → tl s ∼ tl s'


idE : ∀{Γ} → Env Γ Γ
idE {ε} () 
idE {Γ < σ} vze = reflect σ (nvar vze)
idE {Γ < σ} (vsu {σ = σ'} x) = renval {σ = σ'} vsu (idE x)

norm : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
norm t = reify _ (eval idE t)


renvaleval : ∀{Γ Δ E σ} → (γ : Env Δ Γ) → (ρ : Ren Γ E) → (t : Tm Δ σ) → eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) t ≅ renval {σ = σ} ρ (eval γ t)
renvaleval γ ρ (var x) = refl
renvaleval {σ = σ ⇒ τ} γ ρ (lam t) = Σeq 
  ((iext λ Δ' → ext λ (α : Ren _ _) → ext λ v → cong (λ (f : Env _ _) → eval (f << v) t) (iext λ σ' → ext λ x → renvalcomp {σ = σ'} α ρ (γ x))))
  refl
  ((iext λ Δ₁ → iext λ Δ₂ → ext λ (ρ₁ : Ren _ _) → ext λ (ρ₂ : Ren _ _) → ext λ v → fixedtypesleft 
         (cong (λ (f : Env _ _) → renval {σ = τ} ρ₂ (eval (f << v) t)) (iext λ σ' → ext λ x → renvalcomp {σ = σ'} ρ₁ ρ (γ x)))))
renvaleval γ ρ (app {σ}{τ} t u) =  proof
  proj₁ (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) t) renId (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) u) 
  ≅⟨ cong (λ f → proj₁ f renId (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) u)) (renvaleval γ ρ t) ⟩ 
  proj₁ (renval {σ = σ ⇒ τ} ρ (eval γ t)) renId (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) u) 
  ≅⟨ refl ⟩
  proj₁ (eval γ t) ρ (eval (λ {σ'} →  renval {σ = σ'} ρ ∘ γ) u) 
  ≅⟨ cong (proj₁ (eval γ t) ρ) (renvaleval γ ρ u) ⟩
  proj₁ (eval γ t) ρ (renval {σ = σ} ρ (eval γ u))
  ≅⟨ sym (proj₂ (eval γ t) renId ρ (eval γ u)) ⟩
  renval {σ = τ} ρ (proj₁ (eval γ t) renId (eval γ u))
  ∎
renvaleval γ ρ (a ,, b) = cong₂ _,_ (renvaleval γ ρ a) (renvaleval γ ρ b)
renvaleval γ ρ (fst t) = cong proj₁ (renvaleval γ ρ t)
renvaleval γ ρ (snd t) = cong proj₂ (renvaleval γ ρ t)
renvaleval γ ρ ze = refl
renvaleval γ ρ (su t) = cong nsu (renvaleval γ ρ t)
renvaleval {σ = σ} γ ρ (rec z f n) = proof
  natfold {σ = σ} (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) z) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) f) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) n)
  ≅⟨ cong₃ (natfold {σ = σ}) (renvaleval γ ρ z) (renvaleval γ ρ f) (renvaleval γ ρ n) ⟩
  natfold {σ = σ} (renval {σ = σ} ρ (eval γ z))
          ((λ {E} β → proj₁ (eval γ f) (β ∘ ρ)) ,
                                  (λ {Δ₁} {Δ'} ρ₁ ρ' v₁ → trans (proj₂ (eval γ f) (ρ₁ ∘ ρ) ρ' v₁) refl)) 
          (renNf ρ (eval γ n))
  ≅⟨ sym (renvalnatfold {σ = σ} ρ (eval γ z) (eval γ f) (eval γ n)) ⟩
  renval {σ = σ} ρ (natfold {σ = σ} (eval γ z) (eval γ f) (eval γ n))
  ∎
renvaleval γ ρ (hd t) = trans (cong head (renvaleval γ ρ t)) (sym (renvalhead ρ (eval γ t)))
renvaleval γ ρ (tl t) = trans (cong tail (renvaleval γ ρ t)) (sym (renvaltail ρ (eval γ t)))
renvaleval γ ρ (unfold {σ = σ}{τ = τ} z f) = proof
  unFold (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) z) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) f)
  ≅⟨ cong₂ unFold (renvaleval γ ρ z) (renvaleval γ ρ f) ⟩
  unFold {σ = σ}{τ = τ} (renval {σ = σ} ρ (eval γ z)) (renval {σ = σ ⇒ σ ∧ τ} ρ (eval γ f))
  ≅⟨ SVEq (sv-sym (renvalunfold {σ = σ}{τ = τ} ρ (eval γ z) (eval γ f))) ⟩
  streamSV (renval {σ = τ} ρ (proj₂ (proj₁ (eval γ f) renId (eval γ z)))) (∞renvalSV {σ = τ} ρ (∞unFold {σ = σ} (proj₁ (proj₁ (eval γ f) renId (eval γ z))) (eval γ f)))
  ∎


mutual
  renvalId : ∀{Γ σ} → (v : Val Γ σ) → renval {σ = σ} renId v ≅ v
  renvalId {Γ} {ι}   v = NfEq (rennfid v)
  renvalId {Γ} {nat} v = NfEq (rennfid v)
  renvalId {Γ} {σ ⇒ τ} v = Σeq (iext λ E → ext λ a → refl) refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ → ext λ ρ' → ext λ v₁ → fixedtypesright refl)
  renvalId {σ = σ ∧ τ} (a , b) = cong₂ _,_ (renvalId {σ = σ} a) (renvalId {σ = τ} b)
  renvalId {σ = < σ >} s = SVEq (renvalIdSV s)

  renvalIdSV : ∀{Γ σ i} → (v : StreamVal (Val Γ σ) (Ne Γ < σ >)) → _SV∼_ {i} (renvalSV renId v) v
  renvalIdSV (neSV n) = neSV∼ (NeEq (renneid n))
  renvalIdSV {σ = σ} (streamSV h t) = sSV∼ (renvalId {σ = σ} h) (∞renvalIdSV t)

  ∞renvalIdSV : ∀{Γ σ i} → (v : ∞StreamVal (Val Γ σ) (Ne Γ < σ >)) → ∞renvalSV renId v ∞SV⟨ i ⟩∼ v
  ∼force (∞renvalIdSV v) = renvalIdSV (vforce v)


evalsub<< : ∀{Γ Δ σ τ} → (γ : Env Γ Δ) → (u : Tm Γ σ) → (v : Var (Γ < σ) τ) → (γ << eval γ u) v ≅ (eval γ ∘ (sub<< var u)) v
evalsub<< γ u vze = refl
evalsub<< γ u (vsu v) = refl


evalSim : ∀{Γ Δ σ} → {t t' : Tm Γ σ} → {γ γ' : Env Γ Δ} → t ∼ t' → _≅_ {A = Env _ _} γ {B = Env _ _} γ' → eval γ t ≅ eval γ' t'
evalSim (refl∼ {t = t}) q = cong (λ (f : Env _ _) → eval f t) q 
evalSim (sym∼ p) q = sym (evalSim p (sym q))
evalSim (trans∼ p p₁) q = trans (evalSim p q) (evalSim p₁ refl)
evalSim {σ = σ} {γ = γ}{γ' = γ'} (beta∼ {t = t} {u = u}) q = proof
  eval ((λ {σ'} → renval {σ = σ'} renId ∘ γ) << eval γ u) t
  ≅⟨ cong (λ (f : Env _ _) → eval (f << (eval γ u)) t) (iext λ σ' → ext λ x → renvalId {σ = σ'} (γ x)) ⟩
  eval (γ << eval γ u) t
  ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ σ' → ext λ x → evalsub<< γ u x) ⟩
  eval (eval γ ∘ (sub<< var u)) t
  ≅⟨ cong (λ (f : Env _ _) → eval (eval f ∘ (sub<< var u)) t) q ⟩
  eval (eval γ' ∘ (sub<< var u)) t
  ≅⟨ subeval  (sub<< var u) γ' t  ⟩
  eval γ' (sub (sub<< var u) t)
  ∎
evalSim {σ = σ ⇒ τ} {γ = γ}{γ' = γ'} (eta∼ {t = t}) q = Σeq 
  (iext λ Δ → ext λ (ρ : Ren _ _) → ext λ v → lem Δ ρ v) 
  refl 
  ((iext λ Δ → iext λ Δ' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypesleft (cong (renval {σ = τ} ρ') (lem Δ ρ v)))) where 
         lem : ∀ Δ (ρ : Ren _ Δ) v → proj₁ (eval γ t) ρ v ≅ proj₁ (eval ((λ {σ} x → renval {σ = σ} ρ (γ' x)) << v) (ren (λ {σ} → vsu) t)) (λ {σ} x → x) v
         lem Δ ρ v = trans (trans (cong (λ (f : Env _ _) → proj₁ (eval f t) ρ v) q) (sym (cong (λ f → proj₁ f id v) (renvaleval γ' ρ t)))) (cong (λ f → proj₁ f id v) (reneval vsu ((λ {σ} x → renval {σ = σ} ρ (γ' x)) << v) t))
evalSim (congapp∼ p p₁) (q) = cong₂ (λ f g → proj₁ f renId g) (evalSim p q) (evalSim p₁ q)
evalSim {σ = σ ⇒ τ} (conglam∼ {t = t}{t' = t'} p) q = Σeq 
  (iext λ Δ → ext λ (α : Ren _ _) → ext λ v → evalSim p (iext λ σ₁ → cong (λ (f : Env _ _) → (λ {σ'} → renval {σ = σ'} α ∘ f) << v) q)) 
  refl 
  (iext λ Δ → iext λ Δ' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → 
      fixedtypesleft (cong (renval {σ = τ} ρ') (evalSim p (iext λ _ → ext λ x → cong (λ f → ((λ {σ'} x → renval {σ = σ'} ρ (f x)) << v) x) q))))
evalSim (congsc∼ p) q = cong nsu (evalSim p q)
evalSim (congrec∼ z f n) q = cong₃ natfold (evalSim z q) (evalSim f q) (evalSim n q)
evalSim (congreczero∼ z f) refl = refl
evalSim {σ = σ}{γ = γ} (congrecsc∼ z f n) refl = refl
evalSim (congpair∼ a b) q = cong₂ _,_ (evalSim a q) (evalSim b q)
evalSim (congfst∼ p) q = cong proj₁ (evalSim p q)
evalSim (congsnd∼ p) q = cong proj₂ (evalSim p q)
evalSim (congunfold∼ z f) q = cong₂ unFold (evalSim z q) (evalSim f q)
evalSim (conghd∼ p) q = cong head (evalSim p q)
evalSim (congtl∼ p) q = cong tail (evalSim p q)


≅to∼ : ∀{Γ σ} → {t t' : Tm Γ σ} → t ≅ t' → t ∼ t'
≅to∼ refl = refl∼


sub<<ren : ∀{Γ Δ σ τ} → (α : Ren Γ Δ)(u : Tm Γ σ)(y : Var (Γ < σ) τ) → sub<< var (ren α u) (wk α y) ≅ ren α (sub<< var u y)
sub<<ren α u vze = refl
sub<<ren α u (vsu x) = refl

ren∼ : ∀{Γ Δ σ} → {t t' : Tm Γ σ} → {ρ ρ' : Ren Γ Δ} → _≅_ {A = Ren _ _} ρ {B = Ren _ _} ρ' → t ∼ t' → ren ρ t ∼ ren ρ' t'
ren∼ refl refl∼ = refl∼
ren∼ p (sym∼ q) = sym∼ (ren∼ (sym p) q)
ren∼ p (trans∼ q q₁) = trans∼ (ren∼ p q) (ren∼ refl q₁)
ren∼ {ρ = ρ} refl (beta∼ {t = t}{u = u}) = trans∼ (beta∼ {t = ren (wk ρ) t}{u = ren ρ u}) (≅to∼ (
  proof
  sub (sub<< var (ren ρ u)) (ren (wk ρ) t) 
  ≅⟨ subren (sub<< var (ren ρ u)) (wk ρ) t ⟩
  sub ((sub<< var (ren ρ u)) ∘ (wk ρ)) t
  ≅⟨ cong (λ (x : Sub _ _) → sub x t) (iext (λ σ' → ext λ y → sub<<ren ρ u y))  ⟩
  sub (ren ρ ∘ (sub<< var u)) t
  ≅⟨ sym (rensub ρ (sub<< var u) t) ⟩
  ren ρ (sub (sub<< var u) t)
  ∎)) 
ren∼ {ρ = ρ} refl (eta∼ {t = t}) = trans∼ (eta∼ {t = ren ρ t}) (conglam∼ (congapp∼ (≅to∼ (
  proof
  ren vsu (ren ρ t) 
  ≅⟨ sym (rencomp vsu ρ t) ⟩
  ren (vsu ∘ ρ) t 
  ≅⟨ refl ⟩
  ren ((wk ρ) ∘ vsu) t 
  ≅⟨ rencomp (wk ρ) vsu t ⟩
  ren (wk ρ) (ren vsu t)
  ∎)) refl∼))
ren∼ p (congapp∼ q q₁) = congapp∼ (ren∼ p q) (ren∼ p q₁)
ren∼ p (conglam∼ q) = conglam∼ (ren∼ (cong wk p) q)
ren∼ p (congsc∼ n) = congsc∼ (ren∼ p n)
ren∼ p (congrec∼ z f n) = congrec∼ (ren∼ p z) (ren∼ p f) (ren∼ p n)
ren∼ {ρ = ρ} p (congreczero∼ z f) = trans∼ (congreczero∼ (ren ρ z) (ren ρ f)) (ren∼ p refl∼)
ren∼ {ρ = ρ} refl (congrecsc∼ z f n) = congrecsc∼ (ren ρ z) (ren ρ f) (ren ρ n)
ren∼ p (congunfold∼ z f) = congunfold∼ (ren∼ p z) (ren∼ p f)
ren∼ p (conghd∼ q) = conghd∼ (ren∼ p q)
ren∼ p (congtl∼ q) = congtl∼ (ren∼ p q)
ren∼ p (congpair∼ a b) = congpair∼ (ren∼ p a) (ren∼ p b)
ren∼ p (congfst∼ q) = congfst∼ (ren∼ p q)
ren∼ p (congsnd∼ q) = congsnd∼ (ren∼ p q)


mutual
  embNf : ∀{Γ σ} → Nf Γ σ → Tm Γ σ
  embNf (nlam n) = lam (embNf n)
  embNf (ne x) = embNe x
  embNf (a ,-, b) = embNf a ,, embNf b
  embNf nze = ze
  embNf (nsu n) = su (embNf n)
  embNf (nstream h t) = {!!}
  embNf (nunfold z f) = unfold (embNf z) (embNf f)

  embNe : ∀{Γ σ} → Ne Γ σ → Tm Γ σ
  embNe (nvar x) = var x
  embNe (napp t u) = app (embNe t) (embNf u)
  embNe (nfst n) = fst (embNe n)
  embNe (nsnd n) = snd (embNe n)
  embNe (nrec z f n) = rec (embNf z) (embNf f) (embNe n)
  embNe (nhd n) = hd (embNe n)
  embNe (ntl n) = tl (embNe n)
