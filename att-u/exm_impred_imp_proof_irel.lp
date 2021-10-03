require open 
  dk-encodings.att.att
  dk-encodings.att.att-impred
  dk-encodings.att.or
  dk-encodings.att.eq-prop
  dk-encodings.att.true
  dk-encodings.att.false
  dk-encodings.att.exists;


symbol Bool  : El TProp prop ≔ Or ⊤ ⊤;
symbol true  : El Prop Bool  ≔ inl ⊤ ⊤ I-⊤;
symbol false : El Prop Bool  ≔ inr ⊤ ⊤ I-⊤;


symbol not : El TProp (⇝ TProp TProp I prop (λ _, prop)) ≔ λ p, ⇝ Prop Prop I p (λ _, ⊥);


symbol exm : U Prop ≔ ⇝ TProp Prop I prop (λ P, Or P (not P));

symbol ifprop : El Prop (⇝ Prop  Prop I exm  (λ exm_p, 
                         ⇝ TProp Prop I prop (λ P, 
                         ⇝ TProp Prop I prop (λ B, 
                         ⇝ Prop  Prop I P    (λ _, 
                         ⇝ Prop  Prop I P   (λ _, P))))))
     ≔ λ exm_p P B e1 e2,
       or_ind B (not B) (λ _, P) (λ _, e1) (λ _, e2) (exm_p B);

symbol pow : El TProp (⇝ TProp TProp I prop (λ _, prop))
     ≔ λ P, ⇝ Prop Prop I P (λ _, Bool);

symbol retract : El TProp (⇝ TProp TProp I prop (λ _, 
                           ⇝ TProp TProp I prop (λ _, prop)))
     ≔ λ A B, Existsp (⇝ Prop Prop I A (λ _, B)) (λ f,
               Existsp (⇝ Prop Prop I B (λ _, A)) (λ g,
                ⇝ Prop Prop I A (λ x, eqp A (g (f x)) x)));

symbol retract_cond : El TProp (⇝ TProp TProp I prop (λ _, 
                           ⇝ TProp TProp I prop (λ _, prop)))
     ≔ λ A B, Existsp (⇝ Prop Prop I A (λ _, B)) (λ f,
               Existsp (⇝ Prop Prop I B (λ _, A)) (λ g,
                ⇝ Prop Prop I (retract A B) (λ _,
                ⇝ Prop Prop I A (λ x, eqp A (g (f x)) x))));

symbol retract_cond_powA_powB : El Prop (⇝ Prop  Prop I exm  (λ _,
                                         ⇝ TProp Prop I prop (λ A,
                                         ⇝ TProp Prop I prop (λ B, retract_cond (pow A) (pow B)))))
     ≔ λ exm_p A B,
       or_ind (retract_cond (pow A) (pow B)) (not (retract_cond (pow A) (pow B))) 
              (λ _, (retract_cond (pow A) (pow B))) 
              (λ H, H) 
              (λ H, exp 
                     (⇝ Prop Prop I (pow A) (λ _, pow B))  
                     (λ f, Existsp 
                           (⇝ Prop Prop I (pow B) (λ _, pow A)) 
                           (λ g, ⇝ Prop Prop I (retract (pow A) (pow B)) (λ _,
                                 ⇝ Prop Prop I (pow A) (λ x, eqp (pow A) (g (f x)) x))))
                     (λ _ _, false)
                     (exp 
                      (⇝ Prop Prop I (pow B) (λ _, pow A))  
                      (λ g, ⇝ Prop Prop I (retract (pow A) (pow B)) (λ _,
                            ⇝ Prop Prop I (pow A) (λ x, eqp (pow A) (g (λ _, false)) x)))
                      (λ _ _, false)
                      (λ H0, ⊥_ind 
                              (⇝ Prop Prop I (pow A) (λ x, eqp (pow A) (λ _, false) x))
                              (H (exp_ind
                                  (⇝ Prop Prop I (pow A) (λ _, pow B))  
                                  (λ f, Existsp 
                                        (⇝ Prop Prop I (pow B) (λ _, pow A)) 
                                        (λ g, ⇝ Prop Prop I (pow A) (λ x, eqp (pow A) (g (f x)) x)))
                                  (λ _, retract_cond (pow A) (pow B))
                                  (λ powa p_a, exp_ind
                                          (⇝ Prop Prop I (pow B) (λ _, pow A)) 
                                          (λ g, ⇝ Prop Prop I (pow A) (λ x, eqp (pow A) (g (powa x)) x))
                                          (λ _, retract_cond (pow A) (pow B))
                                          (λ powb p_b, 
                                             exp
                                             (⇝ Prop Prop I (pow A) (λ _, pow B))  
                                             (λ f, Existsp 
                                                   (⇝ Prop Prop I (pow B) (λ _, pow A)) 
                                                   (λ g, ⇝ Prop Prop I (retract (pow A) (pow B)) (λ _,
                                                         ⇝ Prop Prop I (pow A) (λ x, eqp (pow A) (g (f x)) x))))
                                             powa
                                             (exp
                                              (⇝ Prop Prop I (pow B) (λ _, pow A))  
                                              (λ g, ⇝ Prop Prop I (retract (pow A) (pow B)) (λ _,
                                                    ⇝ Prop Prop I (pow A) (λ x, eqp (pow A) (g (powa x)) x)))
                                              powb
                                              (λ _, p_b)))
                                          p_a)
                                  H0)))))
              (exm_p (retract_cond (pow A) (pow B)));


symbol U : El TProp prop ≔ ⇝ TProp Prop I prop (λ P, pow P);

symbol proj : El Prop (⇝ Prop Prop I U (λ _, pow U)) 
     ≔ λ u, u U;

symbol π1 : El Prop (⇝ TProp Prop I prop (λ A, 
                     ⇝ TProp Prop I (⇝ Prop TProp I A (λ _, prop)) (λ B, 
                     ⇝ Prop  Prop I (Existsp A B) (λ _, A))))
     ≔ λ A B exAB, exp_ind A B (λ _, A) (λ a b, a) exAB;

symbol π2 : El Prop (⇝ TProp Prop I prop (λ A, 
                     ⇝ TProp Prop I (⇝ Prop TProp I A (λ _, prop)) (λ B, 
                     ⇝ Prop  Prop I (Existsp A B) (λ ex', B (π1 A B ex')))))
     ≔ λ A B exAB, exp_ind A B (λ e, B (π1 A B e)) (λ a b, b) exAB;

compute retract_cond_powA_powB;

symbol inj  : El Prop (⇝ Prop Prop I exm (λ _,
                       ⇝ Prop Prop I (pow U) (λ _, U)));
//     ≔ λ exm_p h P, (π1 _ _ (π2 _ _ (retract_cond_powA_powB exm_p P U)))
//                 (π1 _ _ (retract_cond_powA_powB exm_p U U) h);
