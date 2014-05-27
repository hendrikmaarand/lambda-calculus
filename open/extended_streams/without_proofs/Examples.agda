module Examples where

open import Data.Nat hiding (_<_)

open import Lambda

id : ∀{Γ} → Tm Γ (ι ⇒ ι)
id = lam (var vze)

id' : ∀{Γ} → Tm Γ (ι ⇒ ι)
id' = app (lam (var vze)) (lam (var vze))

fst-proj : ∀{Γ} → Tm Γ (ι ⇒ ι)
fst-proj = fst (id' ,, (su ze))

pair : ∀{Γ} → Tm Γ (nat ∧ nat)
pair = (fst (ze ,, (su ze)) ,, snd (ze ,, (su ze))) 


plus-one : ∀{Γ} → ℕ → Tm Γ nat
plus-one zero = su ze
plus-one (suc n) = su (plus-one n)

stream : ∀{Γ} → Tm Γ < nat >
stream = tup plus-one

stream[1] : ∀{Γ} → Tm Γ nat
stream[1] = proj (suc zero) stream

