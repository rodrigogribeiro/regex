(** Antimirov partial derivatives and its properties *)

Set Implicit Arguments.

Require Import
        Syntax.Regex
        Tactics.LibTactics
        List
        ListSet.


Fixpoint pderiv (a : ascii)(e : regex) : list regex :=
  match e with
  | #0 => empty
  | #1 => empty
  | $ a' =>
    match ascii_dec a a' with
    | left _ => singleton #1
    | right _ => empty                      
    end
  | (e1 @ e2) =>
    match null e1 with
    | left _ =>
      union (pderiv a e2)
            (map (fun e' => e' @ e2)
                 (pderiv a e1))
    | right _ =>
      map (fun e' => e' @ e2) (pderiv a e1)
    end
  | (e1 :+: e2) =>
      union (pderiv a e1) (pderiv a e2)
  | (e1 ^*) =>
     map (fun e' => e' @ (e1 ^*)) (pderiv a e1)
end.

Inductive in_regex_set : string -> list regex -> Prop :=
| Here : forall s e es, s <<- e -> in_regex_set s (e :: es)
| There : forall s e es, in_regex_set s es -> in_regex_set s (e :: es).

Hint Constructors in_regex_set.

Notation "s '<<<-' e" := (in_regex_set s e)(at level 40).

Theorem pderiv_sound
  :  forall e a s
  ,  s <<<- (pderiv a e)
     -> (String a s) <<- e.
Proof.
  induction e ; intros a' s H ; simpl in * ;
    repeat (
        match goal with
        | [H : _ <<<- empty |- _] => inverts* H
        | [H : _ <<<- singleton #1 |- _] => inverts* H
        | [H : _ <<- #1 |- _] => inverts* H
        | [H : _ <<<- nil |- _] => inverts* H                                    
        | [H : context[if ?E then _ else _] |- _] =>
          destruct* E ; substs                             
        end ; eauto).        
Qed.

Theorem pderiv_complete
  : forall e a s
  , (String a s) <<- e ->
    s <<<- (pderiv a e).
Proof.
  induction e ; intros a' s H ; simpl in * ; inverts* H ;
    unfold in_regex_set in * ;
    repeat (match goal with
            | [H : context[if ?E then _ else _] |- _] =>
              destruct* H
            | [ |- context[if ?E then _ else _]] =>
              destruct* E
            | [H : ?a <> ?a |- _] =>
              elim H ; auto
            end ; try solve [econstructor ; eauto]).
  +
    destruct s0 ; simpl in * ; substs.
    apply set_exists__union ; eauto.
    inverts* H5.
    apply set_exists__union.
    lets J : IHe1 H2.
    apply Exists_exists in J.
    destruct J as [x [HIx Hsx]].
    right.
    apply set_exists_map.
    rewrite map_map.
    apply Exists_exists.
    exists (x @ e2) ; split ; eauto.
    remember (pderiv a e1) as L.
    destruct L ; substs.
    inverts* HIx.
    simpl in *.
    inverts* HIx.
    right.
    apply in_map with (f := (fun x0 => x0 @ e2)) in H ; auto.
  +
    destruct s0 ; simpl in * ; substs ; try contradiction ; auto.
    inverts* H5.
    apply Exists_exists.
    lets J : IHe1 H2.
    apply Exists_exists in J.
    destruct J as [x [Hx Hsx]].
    exists (x @ e2) ; split ; eauto.
    apply in_map with (f := (fun e' => e' @ e2)) ; auto.
  +   
    apply set_exists__union ; eauto.
  +
    apply set_exists__union ; eauto.
  +
    inverts* H4.
    lets J : IHe H1.
    apply Exists_exists in J.
    destruct J as [x [Hx Hsx]].
    apply Exists_exists.
    exists (x @ (e ^*)) ; split ; eauto.
    apply in_map with (f := fun e' => e' @ (e ^*)) ; auto.
Qed.

Fixpoint antimirov' (s : string)(e : list regex) : list regex :=
  match s with
  | "" => e
  | String a s' =>
    antimirov' s' (flat_map (pderiv a) e)
  end.

Lemma antimirov'_nil : forall s, antimirov' s nil = nil.
Proof.
  induction s ; simpl in * ; auto.
Qed.  

Definition antimirov s e := antimirov' s (e :: nil).

Lemma antimirov'_sound
  : forall s e
  , "" <<<- (antimirov' s e)
    -> s <<<- e.
Proof.
  induction s ; intros e H ; simpl in * ; auto.
  +
    apply Exists_exists in H.
    destruct H as [x [HIx Hsx]].
    remember (flat_map (pderiv a) e) as L.
    destruct L ; simpl in *.
    *
      rewrite antimirov'_nil in HIx.
      simpl in * ; contradiction.
    *  
      induction e ; simpl in * ; try congruence.