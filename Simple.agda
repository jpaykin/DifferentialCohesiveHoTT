open import Data.Nat using (ℕ; zero)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; [_]; _∷_; _++_; lookup)
open import Data.Product

module Simple where

data Type : Set where
  ∫ ♭ ♯ ℜ ℑ & : Type → Type

data Zone : Set where
  C R D I S : Zone

composeZones : Zone → Zone → Zone
composeZones m D = m
composeZones D m = m
composeZones m C = C
composeZones m S = S
composeZones m I = m
composeZones m R = m

record Ctx : Set where
  constructor [_∣_∣_∣_∣_]
  field
    {cs rs ds is ss} : Data.Nat.ℕ
    Γ : Vec Type cs
    Δ : Vec Type rs
    Θ : Vec Type ds
    Λ : Vec Type is
    Ξ : Vec Type ss

· : ∀ {A : Set} → Vec A ℕ.zero
· = []

open Ctx

appendZone : Zone → Type → Ctx → Ctx
appendZone C t [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ t ∷ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]
appendZone R t [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ t ∷ Δ ∣ Θ ∣ Λ ∣ Ξ ]
appendZone D t [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Δ ∣ t ∷ Θ ∣ Λ ∣ Ξ ]
appendZone I t [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Δ ∣ Θ ∣ t ∷ Λ ∣ Ξ ]
appendZone S t [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ t ∷ Ξ ]

restrict : Zone → Ctx → Ctx
restrict C [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ · ∣ · ∣ · ∣ Ξ ]
restrict R [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Δ ∣ · ∣ · ∣ Ξ ]
restrict D c = c
restrict I [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Λ ∣ · ∣ · ∣ Ξ ]
restrict S [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Ξ ∣ · ∣ · ∣ · ]

data Term (c : Ctx) : Type → Set where
  ♭var : ∀ (v : Fin (cs c)) → Term c (lookup v (Γ c))
  ℜvar : ∀ (v : Fin (rs c)) → Term c (lookup v (Δ c))
  var  : ∀ (v : Fin (ds c)) → Term c (lookup v (Θ c))

  ℜI   : ∀ {τ} → Term [ Γ c ∣ Δ c ∣ · ∣ (Θ c ++ Λ c) ∣ Ξ c ] τ → Term c (ℜ τ)
  ℜE   : ∀ {A B z} → Term (restrict z c) (ℜ A) → Term (appendZone (composeZones z R) A c) B → Term c B

  ℑI   : ∀ {τ} → Term [ Γ c ∣ (Δ c ++ Θ c ++ Λ c) ∣ · ∣ · ∣ Ξ c ] τ → Term c (ℑ τ)
  ℑE   : ∀ {A B z} → Term (restrict z c) (ℑ A) → Term (appendZone (composeZones z I) A c) B → Term c B

  &I   : ∀ {τ} → Term [ Γ c ∣ · ∣ · ∣ (Δ c ++ Θ c ++ Λ c) ∣ Ξ c ] τ → Term c (& τ)
  &E   : ∀ {τ} → Term [ Γ c ∣ (Δ c ++ Θ c ++ Λ c) ∣ · ∣ · ∣ Ξ c ] (& τ) → Term c τ

  ∫I   : ∀ {τ} → Term [ Γ c ∣ (Δ c ++ Θ c ++ Λ c ++ Ξ c) ∣ · ∣ · ∣ · ] τ → Term c (∫ τ)
  ∫E   : ∀ {A B} → Term [ (Γ c ++ Δ c ++ Θ c ++ Λ c ++ Ξ c) ∣ · ∣ · ∣ · ∣ · ] (∫ A) → Term (appendZone S A c) B → Term c B

  ♭I   : ∀ {τ} → Term [ Γ c ∣ · ∣ · ∣ · ∣ (Δ c ++ Θ c ++ Λ c ++ Ξ c) ] τ → Term c (♭ τ)
  ♭E   : ∀ {A B} → Term [ Γ c ∣ (Δ c ++ Θ c ++ Λ c ++ Ξ c) ∣ · ∣ · ∣ · ] (♭ A) → Term (appendZone C A c) B → Term c B

  ♯I   : ∀ {τ} → Term [ (Γ c ++ Δ c ++ Θ c ++ Λ c) ∣ · ∣ · ∣ · ∣ Ξ c ] τ → Term c (♯ τ)
  ♯E   : ∀ {τ} → Term [ Γ c ∣ · ∣ · ∣ · ∣ (Δ c ++ Θ c ++ Λ c ++ Ξ c) ] (♯ τ) → Term c τ

ℜED : ∀ {c A B} → Term c (ℜ A) → Term (appendZone R A c) B → Term c B
ℜED f g = ℜE {z = D} f g

ℑED : ∀ {c A B} → Term c (ℑ A) → Term (appendZone I A c) B → Term c B
ℑED f g = ℑE {z = D} f g

----------------------------------------
-- Experiments

ℜ-counit : ∀ {A} → Term [ · ∣ · ∣ [ ℜ A ] ∣ · ∣ · ] A
ℜ-counit = ℜED (var zero) (ℜvar zero)

ℜ-idem : ∀ {A} → Term [ · ∣ · ∣ [ ℜ A ] ∣ · ∣ · ] (ℜ (ℜ A))
ℜ-idem = ℜED (var zero) (ℜI (ℜI (ℜvar zero)))

ℜ-idem-inv : ∀ {A} → Term [ · ∣ · ∣ [ ℜ (ℜ A) ] ∣ · ∣ · ] (ℜ A)
ℜ-idem-inv = ℜ-counit

ℑ-unit : ∀ {A} → Term [ · ∣ · ∣ [ A ] ∣ · ∣ · ] (ℑ A)
ℑ-unit = ℑI (ℜvar zero)

ℑ-idem : ∀ {A} → Term [ · ∣ · ∣ [ ℑ A ] ∣ · ∣ · ] (ℑ (ℑ A))
ℑ-idem = ℑ-unit

ℑ-idem-inv : ∀ {A} → Term [ · ∣ · ∣ [ ℑ (ℑ A) ] ∣ · ∣ · ] (ℑ A)
ℑ-idem-inv = ℑED (var zero) (ℑE {z = I} (ℜvar zero) (ℑI (ℜvar (suc zero))))

&-counit : ∀ {A} → Term [ · ∣ · ∣ [ & A ] ∣ · ∣ · ] A
&-counit = &E (ℜvar zero)

&-idem : ∀ {A} → Term [ · ∣ · ∣ [ & A ] ∣ · ∣ · ] (& (& A))
&-idem = &I (&I (&E (ℜvar zero)))

&-idem-inv : ∀ {A} → Term [ · ∣ · ∣ [ & (& A) ] ∣ · ∣ · ] (& A)
&-idem-inv = &-counit

∫-unit : ∀ {A} → Term [ · ∣ · ∣ [ A ] ∣ · ∣ · ] (∫ A)
∫-unit = ∫I (ℜvar zero)

∫-idem : ∀ {A} → Term [ · ∣ · ∣ [ ∫ A ] ∣ · ∣ · ] (∫ (∫ A))
∫-idem = ∫-unit

∫-idem-inv : ∀ {A} → Term [ · ∣ · ∣ [ ∫ (∫ A) ] ∣ · ∣ · ] (∫ A)
∫-idem-inv = ∫E (♭var zero) (∫E (♭var (suc zero)) (∫I (ℜvar (suc zero))))

♭-counit : ∀ {A} → Term [ · ∣ · ∣ [ ♭ A ] ∣ · ∣ · ] A
♭-counit = ♭E (ℜvar zero) (♭var zero)

♭-idem : ∀ {A} → Term [ · ∣ · ∣ [ ♭ A ] ∣ · ∣ · ] (♭ (♭ A))
♭-idem = ♭I (♭I (♭E (ℜvar zero) (♭var zero)))

♭-idem-inv : ∀ {A} → Term [ · ∣ · ∣ [ ♭ (♭ A) ] ∣ · ∣ · ] (♭ A)
♭-idem-inv = ♭-counit

♯-unit : ∀ {A} → Term [ · ∣ · ∣ [ A ] ∣ · ∣ · ] (♯ A)
♯-unit = ♯I (♭var zero)

♯-idem : ∀ {A} → Term [ · ∣ · ∣ [ ♯ (♯ A) ] ∣ · ∣ · ] (♯ A)
♯-idem = ♯I (♯E (♯E (♭var zero)))

♯-idem-inv : ∀ {A} → Term [ · ∣ · ∣ [ ♯ A ] ∣ · ∣ · ] (♯ (♯ A))
♯-idem-inv = ♯-unit

adm1 : ∀ {A B} → Term [ · ∣ [ A ] ∣ · ∣ · ∣ · ] B → Term [ [ A ] ∣ · ∣ · ∣ · ∣ · ] B
adm1 f = ℜED (ℜI (♭var zero)) {! wk f!}
