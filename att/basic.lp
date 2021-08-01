require open dk-encodings.att.att;

// Integers
constant symbol Nat : El TSet set;
constant symbol zero : El Set Nat;
constant symbol succ : El Set (⇝ Set Set I Nat (λ _, Nat));
compute El Set (⇝ Set Set I Nat (λ _, Nat));

constant symbol nat_ind : El ∀Prop (⇝ TProp Prop I (⇝ Set TProp I Nat (λ _, prop)) (λ P,
                                    ⇝ Prop  Prop I (P zero) (λ _,
                                    ⇝ Prop  Prop I (⇝ Set  Prop I Nat (λ n,
                                                     ⇝ Prop Prop I (P n) (λ _, P (succ n)))) (λ _,
                                    ⇝ Set   Prop I Nat (λ n, P n)))));

constant symbol nat_rec : El TSet  (⇝ TSet  Set  I (⇝ Set TSet I Nat (λ _, set)) (λ P,
                                    ⇝ Set   Set  I (P zero) (λ _,
                                    ⇝ Set   Set  I (⇝ Set  Set  I Nat (λ n,
                                                     ⇝ Set  Set  I (P n) (λ _, P (succ n)))) (λ _,
                                    ⇝ Set   Set  I Nat (λ n, P n)))));

// Equality
constant symbol eq : El TSet  (⇝ TSet TProp I set (λ A, 
                               ⇝ Set  TProp I A   (λ _,
                               ⇝ Set  TProp I A   (λ _, prop))));

compute El TSet (⇝ TSet TProp I set (λ A, 
                  ⇝ Set  TProp I A   (λ _,
                  ⇝ Set  TProp I A   (λ _, prop))));

constant symbol refl : El ∀Prop (⇝ TSet Prop I set (λ A,
                                 ⇝ Set  Prop I A   (λ a,
                                 ⇝ Set  Prop I A   (λ b, eq A a b))));

compute El ∀Prop (⇝ TSet Prop I set (λ A,
                                 ⇝ Set  Prop I A   (λ a,
                                 ⇝ Set  Prop I A   (λ b, eq A a b))));

constant symbol eq_ind : El ∀Prop (⇝ TSet  ∀Prop I set (λ A,
                                   ⇝ Set   ∀Prop I A   (λ x,   
                                   ⇝ Set   ∀Prop I A   (λ y,
                                   ⇝ Prop  ∀Prop I (eq A x y) (λ _,
                                   ⇝ TProp Prop  I (⇝ Set TProp I A (λ _, prop)) (λ P,
                                   ⇝ Prop  Prop  I (P x) (λ _, P y)))))));

constant symbol eq_rec : El TSet  (⇝ TSet  TSet  I set (λ A,
                                   ⇝ Set   TSet  I A   (λ x,   
                                   ⇝ Set   TSet  I A   (λ y,
                                   ⇝ Prop  TSet  I (eq A x y) (λ _,
                                   ⇝ TSet  Set   I (⇝ Set TSet I A (λ _, set)) (λ P,
                                   ⇝ Set   Set   I (P x) (λ _, P y)))))));

symbol plus : El Set (⇝ Set Set I Nat (λ _,
                      ⇝ Set Set I Nat (λ _, Nat)));

rule plus zero      $x ↪ $x
with plus (succ $x) $y ↪ succ (plus $x $y);



