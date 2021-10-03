require open 
  dk-encodings.att.att
  dk-encodings.att.nat
  dk-encodings.att.eq
  dk-encodings.att.heq
  dk-encodings.att.true
  dk-encodings.att.false;
  
symbol PA1 : El Prop (⇝ Set Prop I Nat (λ x, eq Nat x x)) ≔ refl Nat;

symbol PA2 : El Prop (⇝ Set Prop I Nat (λ x,
                      ⇝ Set Prop I Nat (λ y,
                      ⇝ Prop Prop I (eq Nat x y) (λ _, eq Nat y x))))
     ≔ λ a b p, eq_ind Nat a (λ x _, eq Nat x a) (refl Nat a) b p;

symbol PA3 : El Prop (⇝ Set Prop I Nat (λ x,
                      ⇝ Set Prop I Nat (λ y,
                      ⇝ Set Prop I Nat (λ z,
                      ⇝ Prop Prop I (eq Nat x y) (λ _,
                      ⇝ Prop Prop I (eq Nat y z) (λ _, eq Nat x z)))))) 
     ≔ λ a b c p q, eq_ind Nat b (λ x _, eq Nat a x) p c q;

symbol PA4 : El Prop (⇝ Set Prop I Nat (λ x,
                      ⇝ Set Prop I Nat (λ y,
                      ⇝ Prop Prop I (eq Nat x y) (λ _, eq Nat (succ x) (succ y)))))
     ≔ λ a b p, eq_ind Nat a (λ x _, eq Nat (succ a) (succ x)) (refl Nat (succ a)) b p;

symbol eq_lift : El ∀Prop (⇝ TSet  ∀Prop I set (λ A, 
                           ⇝ Set   ∀Prop  I A   (λ x,   
                           ⇝ Set   ∀Prop I A   (λ y,   
                           ⇝ TSet  Prop I set (λ B, 
                           ⇝ Set   Prop I (⇝ Set Set I A (λ _, B)) (λ f,
                           ⇝ Prop  Prop I (eq A x y) (λ _, eq B (f x) (f y))))))))
     ≔ λ A x y B f p, eq_ind A x (λ y _, eq B (f x) (f y)) (refl B (f x)) y p;

symbol pred ≔ nat_rec (λ _, Nat) zero (λ m _, m);


symbol PA5 : El Prop (⇝ Set Prop I Nat (λ x,
                      ⇝ Set Prop I Nat (λ y,
                      ⇝ Prop Prop I (eq Nat (succ x) (succ y)) (λ _, eq Nat x y))))
     ≔ λ a b p, eq_lift Nat (succ a) (succ b) Nat pred p;

symbol PA6 : El Prop (⇝ Set Prop I Nat (λ x,
                      ⇝ Prop Prop I (eq Nat (succ x) zero) (λ _, ⊥)))
     ≔ λ a p, eq_ind Nat (succ a) (λ x _, nat_hind (λ _, prop) ⊥ (λ _ _, ⊤ ) x) I-⊤ zero p;

symbol plus : El Set (⇝ Set Set I Nat (λ _,
                      ⇝ Set Set I Nat (λ _, Nat)))
     ≔ λ a b, nat_rec (λ _, Nat) b (λ _ n, succ n) a;


symbol times : El Set (⇝ Set Set I Nat (λ _,
                       ⇝ Set Set I Nat (λ _, Nat)))
     ≔ λ a b, nat_rec (λ _, Nat) zero (λ _ n, plus b n) a;

symbol PA7 : El Prop (⇝ Set Prop I Nat (λ x, eq Nat (plus zero x) x))
     ≔ λ a, refl Nat a;

symbol PA8 : El Prop (⇝ Set Prop I Nat (λ x, 
                      ⇝ Set Prop I Nat (λ y, eq Nat (plus (succ x) y) (succ (plus x y)))))
     ≔ λ x y, refl Nat (plus (succ x) y);

symbol PA9 : El Prop (⇝ Set Prop I Nat (λ x, eq Nat (times zero x) zero))
     ≔ λ a, refl Nat zero;

symbol PA10 : El Prop (⇝ Set Prop I Nat (λ x, 
                      ⇝ Set Prop I Nat (λ y, eq Nat (times (succ x) y) (plus y (times x y)))))
     ≔ λ x y, refl Nat (times (succ x) y);

symbol PA11 : El ∀Prop (⇝ TProp Prop I (⇝ Set TProp I Nat (λ _, prop)) (λ P,
                        ⇝ Prop  Prop I (P zero) (λ _,
                        ⇝ Prop  Prop I (⇝ Set  Prop  I Nat (λ n, 
                                         ⇝ Prop Prop  I (P n) (λ _, P (succ n)))) (λ _,
                        ⇝ Set   Prop I Nat (λ n, P n)))))
     ≔ nat_ind;
  
                                                



  

