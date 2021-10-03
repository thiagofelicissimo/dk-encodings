require open 
  dk-encodings.att.att
  dk-encodings.att.att-impred;

symbol Or : El TProp (⇝ TProp TProp  I prop (λ A,
                     ⇝ TProp TProp I prop (λ B, prop))) 
     ≔ λ A B, ⇝ TProp  Prop I prop (λ P,
              ⇝ Prop   Prop I (⇝ Prop Prop I A (λ _, P)) (λ _,
              ⇝ Prop   Prop I (⇝ Prop Prop I B (λ _, P)) (λ _, P)));

symbol inl_or : El Prop (⇝ TProp Prop I prop (λ A,
                      ⇝ TProp Prop I prop (λ B,
                      ⇝ Prop  Prop I A (λ _, Or A B)))) 
     ≔ λ A B a P pa pb, pa a;

symbol inr_or : El Prop (⇝ TProp Prop I prop (λ A,
                      ⇝ TProp Prop I prop (λ B,
                      ⇝ Prop  Prop I B (λ _, Or A B)))) 
     ≔ λ A B b P pa pb, pb b;

symbol el_or : El Prop (⇝ TProp Prop I prop (λ A,
                     ⇝ TProp Prop I prop (λ B,
                     ⇝ TProp Prop I prop (λ P,
                     ⇝ Prop  Prop I (Or A B) (λ _,
                     ⇝ Prop  Prop I (⇝ Prop Prop I A (λ _, P)) (λ _,
                     ⇝ Prop  Prop I (⇝ Prop Prop I B (λ _, P)) (λ _, P)))))))
                       ≔ λ A B P orAB aP bP, orAB P aP bP;

symbol And : El TProp (⇝ TProp TProp  I prop (λ A,
                     ⇝ TProp TProp I prop (λ B, prop))) 
     ≔ λ A B, ⇝ TProp  Prop I prop (λ P,
              ⇝ Prop   Prop I (⇝ Prop Prop I A (λ _, ⇝ Prop Prop I B (λ _, P))) (λ _, P));

symbol in_and : El Prop (⇝ TProp Prop I prop (λ A,
                         ⇝ TProp Prop I prop (λ B,
                         ⇝ Prop  Prop I A (λ _, 
                         ⇝ Prop  Prop I B (λ _, And A B)))))
     ≔ λ A B a b P pab, pab a b;

symbol ell_and : El Prop (⇝ TProp Prop I prop (λ A,
                         ⇝ TProp Prop I prop (λ B,
                         ⇝ Prop  Prop I (And A B) (λ _, A))))
     ≔ λ A B andAB, andAB A (λ a b, a);

symbol elr_and : El Prop (⇝ TProp Prop I prop (λ A,
                         ⇝ TProp Prop I prop (λ B,
                         ⇝ Prop  Prop I (And A B) (λ _, B))))
     ≔ λ A B andAB, andAB B (λ a b, b);

symbol Ex : El TSet  (⇝ TSet  TProp  I set (λ A,
                      ⇝ TProp TProp I (⇝ Set TProp I A (λ _, prop)) (λ _, prop)))
     ≔ λ A B, ⇝ TProp Prop I prop (λ P,
               ⇝ Prop Prop I (⇝ Set Prop I A (λ a, ⇝ Prop Prop I (B a) (λ _, P))) (λ _, P));

symbol ex_in : El Prop   (⇝ TSet Prop I set (λ A,
                         ⇝ TProp Prop I (⇝ Set TProp I A (λ _, prop)) (λ B,
                         ⇝ Set   Prop I A     (λ a,
                         ⇝ Prop  Prop I (B a) (λ _, Ex A B)))))
     ≔ λ A B a b P pab, pab a b;

symbol ex_el : El Prop   (⇝ TSet Prop I set (λ A,
                         ⇝ TProp Prop I (⇝ Set TProp I A (λ _, prop)) (λ B,
                         ⇝ TProp Prop I prop (λ P,
                         ⇝ Prop  Prop I (⇝ Set Prop I A (λ a, ⇝ Prop Prop I (B a) (λ _, P))) (λ _,
                         ⇝ Prop  Prop I (Ex A B) (λ _, P))))))
     ≔ λ A B P p exAB, exAB P p;
