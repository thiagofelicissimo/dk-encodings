require open dk-encodings.att.att;

// Integers
constant symbol Nat : El TSet set;
constant symbol zero : El Set Nat;
constant symbol succ : El Set (⇝ Set Set I Nat (λ _, Nat));
compute El Set (⇝ Set Set I Nat (λ _, Nat));

symbol nat_ind : El ∀Prop (⇝ TProp Prop I (⇝ Set TProp I Nat (λ _, prop)) (λ P,
                           ⇝ Prop  Prop I (P zero) (λ _,
                           ⇝ Prop  Prop I (⇝ Set  Prop I Nat (λ n,
                                            ⇝ Prop Prop I (P n) (λ _, P (succ n)))) (λ _,
                           ⇝ Set   Prop I Nat (λ n, P n)))));

rule nat_ind _ $p0 _ zero ↪ $p0
with nat_ind $P $p0 $ps (succ $n) ↪ $ps $n (nat_ind $P $p0 $ps $n);

symbol nat_rec : El TSet  (⇝ TSet  Set  I (⇝ Set TSet I Nat (λ _, set)) (λ P,
                           ⇝ Set   Set  I (P zero) (λ _,
                           ⇝ Set   Set  I (⇝ Set  Set  I Nat (λ n,
                                            ⇝ Set  Set  I (P n) (λ _, P (succ n)))) (λ _,
                           ⇝ Set   Set  I Nat (λ n, P n)))));

rule nat_rec _ $p0 _ zero ↪ $p0
with nat_rec $P $p0 $ps (succ $n) ↪ $ps $n (nat_rec $P $p0 $ps $n);


// Equality
constant symbol eq : El TSet  (⇝ TSet TProp I set (λ A, 
                               ⇝ Set  TProp I A   (λ _,
                               ⇝ Set  TProp I A   (λ _, prop))));

compute El TSet (⇝ TSet TProp I set (λ A, 
                  ⇝ Set  TProp I A   (λ _,
                  ⇝ Set  TProp I A   (λ _, prop))));

constant symbol refl : El ∀Prop (⇝ TSet Prop I set (λ A,
                                 ⇝ Set  Prop I A   (λ a, eq A a a)));

compute El ∀Prop (⇝ TSet Prop I set (λ A,
                                 ⇝ Set  Prop I A   (λ a, eq A a a)));


symbol eq_ind : El ∀Prop (⇝ TSet  ∀Prop I set (λ A,
                          ⇝ Set   ∀Prop I A   (λ x,   
                          ⇝ TProp  Prop I (⇝ Set TProp I A (λ y, 
                                            ⇝ Prop TProp I (eq A x y) (λ _, prop))) (λ P,
                          ⇝ Prop  Prop I (P x (refl A x)) (λ _,
                          ⇝ Set   Prop I A (λ y, 
                          ⇝ Prop  Prop I (eq A x y) (λ e, P y e)))))));

rule eq_ind $A $x _ $px $x (refl $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?

symbol eq_rec : El ∀Prop (⇝ TSet  ∀Prop I set (λ A,
                          ⇝ Set   ∀Prop I A   (λ x,   
                          ⇝ TProp  Prop I (⇝ Set TProp I A (λ y, 
                                            ⇝ Prop TProp I (eq A x y) (λ _, prop))) (λ P,
                          ⇝ Prop  Prop I (P x (refl A x)) (λ _,
                          ⇝ Set   Prop I A (λ y, 
                          ⇝ Prop  Prop I (eq A x y) (λ e, P y e)))))));

rule eq_rec $A $x _ $px $x (refl $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?

symbol transport : El ∀Prop (⇝ TSet  ∀Prop I set (λ A, 
                           ⇝ Set   ∀Prop  I A   (λ x,   
                           ⇝ Set   ∀Prop I A   (λ y,   
                           ⇝ TSet  Prop I set (λ B, 
                           ⇝ Set   Prop I (⇝ Set Set I A (λ _, B)) (λ f,
                           ⇝ Prop  Prop I (eq A x y) (λ _, eq B (f x) (f y))))))))
     ≔ λ A x y B f p, eq_ind A x (λ y _, eq B (f x) (f y)) (refl B (f x)) y p;

symbol plus : El Set (⇝ Set Set I Nat (λ _,
                      ⇝ Set Set I Nat (λ _, Nat))) ≔ λ n m, nat_rec (λ _, Nat) m (λ _ acc, succ acc) n;

compute plus (succ zero) zero;



