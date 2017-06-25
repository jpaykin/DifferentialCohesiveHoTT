open import Data.Nat using (ℕ; zero)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; [_]; _∷_; _++_; lookup)
open import Data.Product
module Simple where

data Type (Base : Set) : Set where
  ∫ ♭ ♯ ℜ ℑ & : Type Base → Type Base
  base : Base → Type Base

data Zone : Set where
  C R D I S : Zone

composeZones : Zone → Zone → Zone
composeZones m D = m
composeZones D m = m
composeZones m C = C
composeZones m S = S
composeZones m I = m
composeZones m R = m

record Ctx (Base : Set ): Set where
  constructor [_∣_∣_∣_∣_]
  field
    {cs rs ds is ss} : Data.Nat.ℕ
    Γ : Vec (Type Base) cs
    Δ : Vec (Type Base) rs
    Θ : Vec (Type Base) ds
    Λ : Vec (Type Base) is
    Ξ : Vec (Type Base) ss

· : ∀ {A : Set} → Vec A ℕ.zero
· = []

open Ctx

appendZone : ∀ {Base} → Zone → Type Base → Ctx Base → Ctx Base
appendZone C t [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ t ∷ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]
appendZone R t [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ t ∷ Δ ∣ Θ ∣ Λ ∣ Ξ ]
appendZone D t [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Δ ∣ t ∷ Θ ∣ Λ ∣ Ξ ]
appendZone I t [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Δ ∣ Θ ∣ t ∷ Λ ∣ Ξ ]
appendZone S t [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ t ∷ Ξ ]

restrict : ∀ {Base} → Zone → Ctx Base → Ctx Base
restrict C [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ · ∣ · ∣ · ∣ Ξ ]
restrict R [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Δ ∣ · ∣ · ∣ Ξ ]
restrict D c = c
restrict I [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Λ ∣ · ∣ · ∣ Ξ ]
restrict S [ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ] = [ Γ ∣ Ξ ∣ · ∣ · ∣ · ]

data Term {Base : Set} (c : Ctx Base) : Type Base → Set where
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
  ∫E   : ∀ {A B} → Term [ (Γ c) ∣ ( Δ c ++ Θ c ++ Λ c ++ Ξ c) ∣ · ∣ · ∣ · ] (∫ A) → Term (appendZone S A c) B → Term c B

  ♭I   : ∀ {τ} → Term [ Γ c ∣ · ∣ · ∣ · ∣ (Δ c ++ Θ c ++ Λ c ++ Ξ c) ] τ → Term c (♭ τ)
  ♭E   : ∀ {A B} → Term [ Γ c ∣ (Δ c ++ Θ c ++ Λ c ++ Ξ c) ∣ · ∣ · ∣ · ] (♭ A) → Term (appendZone C A c) B → Term c B

  ♯I   : ∀ {τ} → Term [ (Γ c ++ Δ c ++ Θ c ++ Λ c) ∣ · ∣ · ∣ · ∣ Ξ c ] τ → Term c (♯ τ)
  ♯E   : ∀ {τ} → Term [ Γ c ∣ · ∣ · ∣ · ∣ (Δ c ++ Θ c ++ Λ c ++ Ξ c) ] (♯ τ) → Term c τ

ℜED : ∀ {Base c A B} → Term {Base = Base} c (ℜ A) → Term (appendZone R A c) B → Term c B
ℜED f g = ℜE {z = D} f g

ℑED : ∀ {Base c A B} → Term {Base = Base} c (ℑ A) → Term (appendZone I A c) B → Term c B
ℑED f g = ℑE {z = D} f g

----------------------------------------
-- Experiments

ℜ-counit : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ℜ A ] ∣ · ∣ · ] A
ℜ-counit = ℜED (var zero) (ℜvar zero)

ℜ-idem : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ℜ A ] ∣ · ∣ · ] (ℜ (ℜ A))
ℜ-idem = ℜED (var zero) (ℜI (ℜI (ℜvar zero)))

ℜ-idem-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ℜ (ℜ A) ] ∣ · ∣ · ] (ℜ A)
ℜ-idem-inv = ℜ-counit

ℑ-unit : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ A ] ∣ · ∣ · ] (ℑ A)
ℑ-unit = ℑI (ℜvar zero)

ℑ-idem : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ℑ A ] ∣ · ∣ · ] (ℑ (ℑ A))
ℑ-idem = ℑ-unit

ℑ-idem-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ℑ (ℑ A) ] ∣ · ∣ · ] (ℑ A)
ℑ-idem-inv = ℑED (var zero) (ℑE {z = I} (ℜvar zero) (ℑI (ℜvar (suc zero))))

&-counit : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ & A ] ∣ · ∣ · ] A
&-counit = &E (ℜvar zero)

&-idem : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ & A ] ∣ · ∣ · ] (& (& A))
&-idem = &I (&I (&E (ℜvar zero)))

&-idem-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ & (& A) ] ∣ · ∣ · ] (& A)
&-idem-inv = &-counit

∫-unit : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ A ] ∣ · ∣ · ] (∫ A)
∫-unit = ∫I (ℜvar zero)

∫-idem : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ∫ A ] ∣ · ∣ · ] (∫ (∫ A))
∫-idem = ∫-unit

∫-idem-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ∫ (∫ A) ] ∣ · ∣ · ] (∫ A)
∫-idem-inv = ∫E (ℜvar zero) (∫E ((ℜvar (suc zero))) (∫I ((ℜvar (suc zero)))))

♭-counit : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♭ A ] ∣ · ∣ · ] A
♭-counit = ♭E (ℜvar zero) (♭var zero)

♭-idem : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♭ A ] ∣ · ∣ · ] (♭ (♭ A))
♭-idem = ♭I (♭I (♭E (ℜvar zero) (♭var zero)))

♭-idem-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♭ (♭ A) ] ∣ · ∣ · ] (♭ A)
♭-idem-inv = ♭-counit

♯-unit : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ A ] ∣ · ∣ · ] (♯ A)
♯-unit = ♯I (♭var zero)

♯-idem : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♯ (♯ A) ] ∣ · ∣ · ] (♯ A)
♯-idem = ♯I (♯E (♯E (♭var zero)))

♯-idem-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♯ A ] ∣ · ∣ · ] (♯ (♯ A))
♯-idem-inv = ♯-unit

ℜ♭-is-♭ : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ℜ (♭ A) ] ∣ · ∣ · ] (♭ A)
ℜ♭-is-♭ = ℜED (var zero) (ℜvar zero)

ℜ♭-is-♭-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♭ A ] ∣ · ∣ · ] (ℜ (♭ A))
ℜ♭-is-♭-inv = ♭E (ℜvar zero) (ℜI (♭I (♭var zero)))

♭ℜ-is-♭ : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♭ (ℜ A) ] ∣ · ∣ · ] (♭ A)
♭ℜ-is-♭ = ♭E (ℜvar zero) (ℜE {z = C} (♭var zero) (♭I (♭var zero)))

♭ℜ-is-♭-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♭ A ] ∣ · ∣ · ] (♭ (ℜ A))
♭ℜ-is-♭-inv = ♭E (ℜvar zero) (♭I (ℜI (♭var zero)))

ℑ♭-is-♭ : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ℑ (♭ A) ] ∣ · ∣ · ] (♭ A)
ℑ♭-is-♭ = ℑED (var zero) (♭E (ℜvar (suc zero)) (♭I (♭var zero)))

ℑ♭-is-♭-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♭ A ] ∣ · ∣ · ] (ℑ (♭ A))
ℑ♭-is-♭-inv = ♭E (ℜvar zero) (ℑI (ℜvar zero))

♭ℑ-is-♭ : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♭ (ℑ A) ] ∣ · ∣ · ] (♭ A)
♭ℑ-is-♭ = ♭E (ℜvar zero) (ℑE {z = C} (♭var zero) (♭I (♭var zero)))

♭ℑ-is-♭-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♭ A ] ∣ · ∣ · ] (♭ (ℑ A))
♭ℑ-is-♭-inv = ♭E (ℜvar zero) (♭I (ℑI (♭var zero)))

♯ℜ-is-♯ : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♯ (ℜ A) ] ∣ · ∣ · ] (♯ A)
♯ℜ-is-♯ = ♯I (ℜE {z = C} (♯E (♭var zero)) (♭var zero))

♯ℜ-is-♯-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♯ A ] ∣ · ∣ · ] (♯ (ℜ A))
♯ℜ-is-♯-inv = ♯I (ℜI (♯E (♭var zero)))

ℜ♯-is-♯ : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ℜ (♯ A) ] ∣ · ∣ · ] (♯ A)
ℜ♯-is-♯ = ℜED (var zero) (ℜvar zero)

ℜ♯-is-♯-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ♯ A ] ∣ · ∣ · ] (ℜ (♯ A))
ℜ♯-is-♯-inv = ℜI (♯I (♯E (♭var zero)))

ℜ∫-is-∫ : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ℜ (∫ A) ] ∣ · ∣ · ] (∫ A)
ℜ∫-is-∫ = ℜED (var zero) (ℜvar zero)

ℜ∫-is-∫-inv : ∀ {Base A} → Term {Base = Base} [ · ∣ · ∣ [ ∫ A ] ∣ · ∣ · ] (ℜ (∫ A))
ℜ∫-is-∫-inv = ∫E (ℜvar zero) (ℜI (∫I (ℜvar (suc zero))))


-- adm1 : ∀ {Base A B} → Term {Base = Base} [ · ∣ [ A ] ∣ · ∣ · ∣ · ] B → Term [ [ A ] ∣ · ∣ · ∣ · ∣ · ] B
-- adm1 f = ℜED (ℜI (♭var zero)) {! wk f!}

