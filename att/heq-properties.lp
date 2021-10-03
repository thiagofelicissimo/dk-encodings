require open dk-encodings.att.att;
require open dk-encodings.att.heq;

symbol heq_transport : El TSet  (⇝ TSet TSet I set (λ A, 
                                 ⇝ TSet Set I set (λ B, 
                                 ⇝ Prop Set I (heq set A B) (λ _, 
                                 ⇝ Set  Set I A (λ _, B))))) ≔
  λ A B p a, heq_rec set A (λ y _, y) a B p;
