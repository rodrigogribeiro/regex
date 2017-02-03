(** Definition of regular expression syntax *)

Set Implicit Arguments.

Require Export
        Tactics.LibTactics
        Ascii
        Relation_Definitions
        Setoid
        String
        DecidableTypeEx.

Open Scope string_scope.

Lemma str_append_nil_end : forall s, s ++ "" = s.
Proof.
  induction s ; simpl in * ; fequals*.
Qed.

Lemma str_append_rewind
  : forall a s s'
  , String a (s ++ s') = (String a s) ++ s'.
Proof.
  intros a s s' ; reflexivity.
Qed.  

Inductive regex : Set :=
| Emp : regex  
| Eps : regex          
| Chr : ascii -> regex
| Cat : regex -> regex -> regex
| Choice : regex -> regex -> regex
| Star : regex -> regex.                               

Notation "'#0'" := Emp.
Notation "'#1'" := Eps.
Notation "'$' c" := (Chr c)(at level 40).
Notation "e '@' e1" := (Cat e e1)(at level 15, left associativity).
Notation "e ':+:' e1" := (Choice e e1)(at level 20, left associativity).
Notation "e '^*'" := (Star e)(at level 40).
  
(** Semantics of regular expressions *)

Reserved Notation "s '<<-' e" (at level 40).

Inductive in_regex : string -> regex -> Prop :=
| InEps
  : "" <<- #1
| InChr
  : forall c
  , (String c EmptyString) <<- ($ c)
| InCat
  :  forall e e' s s' s1
  ,  s <<- e
  -> s' <<- e'
  -> s1 = s ++ s'
  -> s1 <<- (e @ e')
| InLeft
  :  forall s e e'
  ,  s <<- e
  -> s <<- (e :+: e')
| InRight
  :  forall s' e e'
  ,  s' <<- e'
  -> s' <<- (e :+: e')
| InStarLeft
  : forall e
  , "" <<- (e ^*)
| InStarRight              
  : forall s s' s1 a e
  ,  (String a s) <<- e
  -> s' <<- (e ^*)
  -> s1 = String a (s ++ s')
  -> s1 <<- (e ^*)                          
where "s '<<-' e" := (in_regex s e).

Hint Constructors in_regex.

Ltac inverts_in_regex :=
  match goal with
  | [H : _ <<- _ |- _] => inverts H  
  end.

Lemma empty_string_concat
  : forall (s s' : string)
  , "" = s ++ s'
  -> s = "" /\ s' = "".
Proof.
  intros ; destruct s ; destruct s' ; splits ; simpl in * ; try congruence.
Qed.  

Hint Immediate empty_string_concat.

(** nullability test *)
            
Definition null : forall (e : regex), { "" <<- e } + { ~ ("" <<- e) }.
  refine (fix null_rec (e : regex) : { "" <<- e } + { ~ ("" <<- e) } :=
     match e as e1 return e = e1 -> { "" <<- e1 } + { ~ ("" <<- e1) } with
     | #0 => fun _ =>
       right _
     | #1 => fun _ =>
       left _
     | $ _ => fun _ =>
       right _
     | (e1 @ e2) => fun _ =>
       match null_rec e1 with
       | left Hl =>
         match null_rec e2 with
         | left Hr =>
           left (InCat Hl Hr eq_refl)
         | right _ =>
           right _
         end  
       | right _ =>
         right _
       end
     | (e1 :+: e2) => fun _ =>
       match null_rec e1 with
       | left Hl =>
         left (InLeft _ Hl)
       | right _ =>
         match null_rec e2 with
         | left Hr =>
           left (InRight _ Hr)
         | right _ =>
           right _
         end        
       end
     | (e1 ^*) => fun _ =>
        left (InStarLeft _)
        end eq_refl) ; clear null_rec ;
       try intro ; try inverts_in_regex ;
       try 
         (match goal with
          | [H : "" = _ ++ _ |- _] =>
            apply empty_string_concat in H ;
            destruct H ;
            substs ;
            try contradiction                        
          end) ; jauto.
Defined.


(** equivalence *)


Definition regex_equiv (e e' : regex) : Prop :=
  forall s, s <<- e <-> s <<- e'.

Lemma regex_equiv_refl : Reflexive regex_equiv.
Proof.
  unfolds ; unfolds regex_equiv ; intros ; splits ; auto.
Qed.

Lemma regex_equiv_sym : Symmetric regex_equiv.
Proof.  
  unfolds ; unfolds regex_equiv ; intros x y H s ; splits ; intros H1 ;
  lets J : H s ; destruct* J.
Qed.

Lemma regex_equiv_trans : Transitive regex_equiv.
Proof.
  unfolds ; unfolds regex_equiv ; intros x y z H1 H2 s ; splits ; intros H3 ;
  lets J : H1 s ;
  lets K : H2 s ;
  destruct* J ; destruct* K.
Qed.

Instance regex_equiv_Equiv : Equivalence regex_equiv.
Proof.
  split ;
    [ apply regex_equiv_refl
    | apply regex_equiv_sym
    | apply regex_equiv_trans ].
Qed.

Definition regex_eq_dec (e e' : regex) : {e = e'} + {e <> e'}.
  pose ascii_dec.
  decide equality.
Defined.  

(* regex is an decidable type *)

Module Regex_as_DT <: UsualDecidableType.

  Definition t := regex.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition eq_dec := regex_eq_dec.
  Definition eq_equiv : Equivalence eq.
  Proof.
    split ; unfolds ;
      [ apply eq_refl
      | apply eq_sym
      | apply eq_trans ].
  Qed.  
End Regex_as_DT.  

  