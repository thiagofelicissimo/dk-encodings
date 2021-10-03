require open dk-encodings.att.att;
require open dk-encodings.att.basic;

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

symbol pred ≔ nat_rec (λ _, Nat) zero (λ m _, m);

symbol PA5 : El Prop (⇝ Set Prop I Nat (λ x,
                      ⇝ Set Prop I Nat (λ y,
                      ⇝ Prop Prop I (eq Nat (succ x) (succ y)) (λ _, eq Nat x y))))
     ≔ λ a b p, transport Nat (succ a) (succ b) Nat pred p;


