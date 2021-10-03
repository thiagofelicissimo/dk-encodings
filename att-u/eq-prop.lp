require open dk-encodings.att.att;

// type
constant symbol eqp : Π A : U Prop, El Prop A → El Prop A → U Prop;

// constructor
constant symbol reflp : Π (A : U Prop) (a : El Prop A), El Prop (eqp A a a);

// eliminators

// into Prop
symbol eqp_ind : Π (A : U Prop)
                  (x : El Prop A)
                  (P : Π y : El Prop A, El Prop (eqp A x y) → U Prop)
                  (_ : El Prop (P x (reflp A x)))
                  (y : El Prop A)
                  (e : El Prop (eqp A x y)),
                  El Prop (P y e);

// into TProp (large)
symbol eqp_hind : Π (A : U Prop)
                  (x : El Prop A)
                  (P : Π y : El Prop A, El Prop (eqp A x y) → U TProp)
                  (_ : El TProp (P x (reflp A x)))
                  (y : El Prop A)
                  (e : El Prop (eqp A x y)),
                  El TProp (P y e);

// into Set (large)
symbol eqp_rec : Π (A : U Prop)
                  (x : El Prop A)
                  (P : Π y : El Prop A, El Prop (eqp A x y) → U Set)
                  (_ : El Set (P x (reflp A x)))
                  (y : El Prop A)
                  (e : El Prop (eqp A x y)),
                  El Set (P y e);

// into TSet (large)
symbol eqp_hrec : Π (A : U Prop)
                  (x : El Prop A)
                  (P : Π y : El Prop A, El Prop (eqp A x y) → U TSet)
                  (_ : El TSet (P x (reflp A x)))
                  (y : El Prop A)
                  (e : El Prop (eqp A x y)),
                  El TSet (P y e);

// computation rules                
rule eqp_ind $A $x _ $px $x (reflp $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
rule eqp_hind $A $x _ $px $x (reflp $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
rule eqp_rec $A $x _ $px $x (reflp $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
rule eqp_hrec $A $x _ $px $x (reflp $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
