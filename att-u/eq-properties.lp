require open dk-encodings.att.att;
require open dk-encodings.att.eq;

symbol eq_lift : El ∀Prop (⇝ TSet  ∀Prop I set (λ A, 
                           ⇝ Set   ∀Prop  I A   (λ x,   
                           ⇝ Set   ∀Prop I A   (λ y,   
                           ⇝ TSet  Prop I set (λ B, 
                           ⇝ Set   Prop I (⇝ Set Set I A (λ _, B)) (λ f,
                           ⇝ Prop  Prop I (eq A x y) (λ _, eq B (f x) (f y))))))))
     ≔ λ A x y B f p, eq_ind A x (λ y _, eq B (f x) (f y)) (refl B (f x)) y p;

//symbol eq_transport : El ∀Prop (⇝ TSet  ∀Prop I set (λ A, 
//                           ⇝ Set   ∀Prop I A   (λ x,   
//                           ⇝ Set   ∀Prop I A   (λ y,   
//                           ⇝ TSet  Prop I set (λ B, 
//                           ⇝ Set   Prop I (⇝ Set Set I A (λ _, B)) (λ f,
//                           ⇝ Prop  Prop I (eq A x y) (λ _, eq B (f x) (f y))))))))



