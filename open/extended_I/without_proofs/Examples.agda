module Examples where

open import Lambda

0,1,2 : ∀{Γ} → Tm Γ [ nat ]
0,1,2 = cons ze (cons (su ze) (cons (su (su ze)) nil))


add : ∀{Γ} → Tm Γ (nat ⇒ nat ⇒ nat)
add = lam (lam (rec (var vze) (lam (su (var vze))) (var (vsu vze)))) 

-- app (app add (su (su ze))) (su (su ze))

mult : ∀{Γ} → Tm Γ (nat ⇒ nat ⇒ nat)
mult = lam (lam 
               (rec 
                   ze 
                   (lam (app (app add (var (vsu vze))) (var vze))) 
                   (var (vsu vze))))



folded : ∀{Γ} → Tm Γ nat
folded = fold ze add 0,1,2