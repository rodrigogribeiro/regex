(** Brzozowski derivatives and its properties *)

Set Implicit Arguments.

Require Import
        Syntax.Regex
        Derivatives.Smart.

Fixpoint deriv (a : ascii)(e : regex) : regex :=
  match e with
  | #0 => #0
  | #1 => #0
  | $ c =>
    match ascii_dec a c with
    | left _ => #1
    | right _ => #0              
    end
  | (e1 @ e2) =>
    match null e1 with
    | left _ =>
      ((deriv a e1) :@: e2) :++: (deriv a e2)
    | right _ =>
      (deriv a e1) :@: e2
    end  
  | (e1 :+: e2) =>
    (deriv a e1) :++: (deriv a e2)
  | (e1 ^*) =>
     (deriv a e1) :@: (e1 :^*:)
  end.  

Theorem deriv_sound
  : forall e a s
  , s <<- (deriv a e)
    -> (String a s) <<- e.
Proof.
  Local Hint Immediate
        cat_smart_sound
        cat_smart_complete
        choice_smart_sound
        choice_smart_complete
        star_smart_sound
        star_smart_complete.
  induction e ; intros a' s H ; simpl in * ; try solve [ inverts* H ] ;
    repeat (match goal with
            | [H : _ <<- #0 |- _] =>
              inverts* H
            | [H : _ <<- #1 |- _] =>
              inverts* H
            | [H : context[if ?E then _ else _] |- _] =>
               destruct* E
            end ; substs*).
  +
    lets J : choice_smart_sound H.
    inverts* J.
    lets K : cat_smart_sound H2.
    inverts* K.
  +
    lets J : cat_smart_sound H.
    inverts* J.
  +
    lets J : choice_smart_sound H.
    inverts* J.
  +
    lets J : cat_smart_sound H.
    inverts* J.
Qed.

Hint Immediate deriv_sound.
            
Theorem deriv_complete
  :  forall e a s
  ,  (String a s) <<- e
  -> s <<- deriv a e.
Proof.
  Local Hint Immediate
        cat_smart_sound
        cat_smart_complete
        choice_smart_sound
        choice_smart_complete
        star_smart_sound
        star_smart_complete.
  induction e ; intros a' s H ; simpl in * ;
    repeat (match goal with
            | [H : _ <<- #0 |- _] =>
              inverts* H
            | [H : _ <<- #1 |- _] =>
              inverts* H
            | [H : _ <<- ($ _) |- _] =>
              inverts* H
            | [H : context[if ?E then _ else _] |- _] =>
              destruct* E
            | [|- context[if ?E then _ else _]] =>
              destruct* E
            | [H : ?a <> ?a |- _] =>
              elim H ; reflexivity
            end ; substs*). 
  +
    inverts* H.
    destruct* s0.
    - 
      simpl in *. substs*.
      apply choice_smart_complete.
      apply InRight ; auto.
    -
      inverts* H5.
      apply choice_smart_complete.
      apply InLeft.
      apply cat_smart_complete ; eauto.
  +
    inverts* H.
    apply cat_smart_complete.
    destruct* s0.
    -
      contradiction.
    -
      inverts* H5.
  +
    apply choice_smart_complete.
    inverts* H.
  +
    inverts* H.
    inverts* H2.
    -
      inverts* H4.
      rewrite str_append_nil_end.
      apply cat_smart_complete.
      eapply InCat ; eauto.
      rewrite str_append_nil_end ; auto.
    -
      apply cat_smart_complete.
      inverts* H4.
      eapply InCat.
      eapply IHe ; eauto.
      eapply star_smart_complete.
      eapply InStarRight.
      exact H0.
      exact H3.
      eauto.
      eauto.
Qed.    

Hint Immediate deriv_complete.
            
Fixpoint brzozowski (s : string)(e : regex) : regex :=
  match s with
  | "" => e
  | (String a s') =>
    brzozowski s' (deriv a e)
  end.  

Theorem brzozowski_sound
  :  forall s e
  ,  "" <<- (brzozowski s e)
  -> s <<- e.
Proof.
  induction s ; destruct e ; intros ; simpl in * ;
    repeat (match goal with
            | [H : _ <<- #0 |- _] =>
              inverts* H
            | [H : _ <<- #1 |- _] =>
              inverts* H             
            | [H : context[if ?E then _ else _] |- _] =>
              destruct* E
            | [|- context[if ?E then _ else _]] =>
              destruct* E
            | [H : _ <<- ($ _) |- _] =>
              inverts* H
            | [H : ?a <> ?a |- _] =>
              elim H ; reflexivity                         
            end) ; substs* ; eauto
    ; try solve
          [ lets J : IHs H
          ; inverts* J].
  +
    lets J : IHs H.
    lets K : choice_smart_sound J.
    inverts* K.
    lets L : cat_smart_sound H2.
    apply deriv_sound ; simpl ; auto.
    destruct* (null e1).
  +
    lets J : IHs H.
    lets K : cat_smart_sound J.
    inverts* K.
  +
    lets J : IHs H.
    lets K : choice_smart_sound J.
    inverts* K.
  +
    lets J : IHs H.
    lets K : cat_smart_sound J.
    inverts* K.
Qed.

Theorem brzozowski_complete
  :  forall s e
  ,  s <<- e
  -> "" <<- (brzozowski s e).
Proof.
  Local Hint Immediate
        cat_smart_sound
        cat_smart_complete
        choice_smart_sound
        choice_smart_complete
        star_smart_sound
        star_smart_complete.  
  induction s ; destruct e ; intros ; simpl in * ;
    repeat (match goal with
            | [H : _ <<- #0 |- _] =>
              inverts* H
            | [H : _ <<- #1 |- _] =>
              inverts* H             
            | [H : context[if ?E then _ else _] |- _] =>
              destruct* E
            | [|- context[if ?E then _ else _]] =>
              destruct* E
            | [H : _ <<- ($ _) |- _] =>
              inverts* H
            | [H : ?a <> ?a |- _] =>
              elim H ; reflexivity                         
            end) ; substs* ; eauto.
  +
    eapply IHs.
    inverts* H.
    eapply choice_smart_complete.
    destruct s0 ; simpl in * ; substs*.
    -  
      inverts* H5.
      eapply InLeft ; eauto.
      eapply cat_smart_complete ; eauto.
  +
    inverts* H.
    destruct s0 ; try contradiction ; simpl in * ; eauto.
    inverts* H5.
    apply IHs.
    eapply cat_smart_complete.
    eapply InCat ; eauto.    
  +
    inverts* H.
    -
      apply IHs.
      apply choice_smart_complete.
      apply InLeft ; apply deriv_complete ; eauto.
    -
      apply IHs.
      apply choice_smart_complete.
      apply InRight ; apply deriv_complete ; eauto.
  +
    inverts* H.
    inverts* H4.
    apply IHs.
    apply cat_smart_complete ; eauto.
Qed.    