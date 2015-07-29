Require Import SfLib.

(* Terms *)

Inductive tm : Type :=
| var : id -> tm
| star : tm
| app : tm -> tm -> tm
| abs : id -> tm -> tm -> tm
| pi : id -> tm -> tm -> tm
| castu : tm -> tm -> tm
| castd : tm -> tm
| mu : id -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Variable" | Case_aux c "TypeofTypes" 
    | Case_aux c "Application" | Case_aux c "Abstraction" 
    | Case_aux c "Dependent Product" | Case_aux c "CastUp"
    | Case_aux c "Cast Down" | Case_aux c "Polymorphic Recursion"].

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(* Values *)

Inductive value : tm -> Prop :=
| v_star : value (star)
| v_abs : forall x t e, value (abs x t e)
| v_pi : forall x t t', value (pi x t t')
| v_castu : forall t e, value (castu t e).

Hint Constructors value.


(* Substition *)
(* Only consider simple situations, where we only substitute closed terms  *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).


Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | var x' => if eq_id_dec x x' then s else t
  | star => star
  | app t1 t2 =>
      app ([x:=s]t1) ([x:=s]t2)
  | abs x' T t1 =>
      abs x' T (if eq_id_dec x x' then t1 else ([x:=s]t1))
  | pi x' T t1 =>
      pi x' T (if eq_id_dec x x' then t1 else ([x:=s]t1))
  | castu t e => castu ([x:=s]t) ([x:=s]e)
  | castd e => castd ([x:=s]e)
  | mu x' T t1 =>
      mu x' T (if eq_id_dec x x' then t1 else ([x:=s]t1))
  end

where "'[' x ':=' s ']' t" := (subst x s t).


(* Operational Semantics *)

Reserved Notation "t1 '=>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| S_Beta : forall x t e1 e2, app (abs x t e1) e2 => [x:=e2]e1
| S_CastDownUp : forall t e, castd (castu t e) => e
| S_App : forall e1 e1' e2, e1 => e1' -> app e1 e2 => app e1' e2
| S_CastDown : forall e e', e => e' -> castd e => castd e'
| S_Mu : forall x t e, mu x t e => [x:=(mu x t e)]e

where "t1 '=>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "S_Beta" | Case_aux c "S_CastDownUp" 
  | Case_aux c "ST_App" | Case_aux c "S_CastDown" 
  | Case_aux c "ST_Mu"].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '=>*' t2" := (multistep t1 t2) (at level 40).

(* Typing *)

(* Contexts *)

Definition context := partial_map tm.

(* Typing Relation *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> tm -> Prop :=
| T_Ax : forall Gamma, Gamma |- star \in star
| T_Var : forall Gamma x t,
    Gamma x = Some t -> Gamma |- (var x) \in t
| T_App : forall Gamma x t1 t2 e1 e2,
    Gamma |- e1 \in pi x t2 t1 ->
    Gamma |- e2 \in t2 ->
    Gamma |- app e1 e2 \in [x:=e2]t1
| T_Lam : forall Gamma x t1 t2 e,
    extend Gamma x t1 |- e \in t2 ->
    Gamma |- pi x t1 t2 \in star ->
    Gamma |- abs x t1 e \in pi x t1 t2
| T_Pi : forall Gamma x t1 t2,
    Gamma |- t1 \in star ->
    extend Gamma x t1 |- t2 \in star ->
    Gamma |- pi x t1 t2 \in star
| T_CastUp : forall Gamma t1 t2 e,
    Gamma |- e \in t2 ->
    Gamma |- t1 \in star ->
    t1 => t2 ->
    Gamma |- castu t1 e \in t1
| T_CastDown : forall Gamma e t1 t2,
    Gamma |- e \in t1 ->
    Gamma |- t2 \in star ->
    t1 => t2 ->
    Gamma |- castd e \in t2
| T_Mu : forall Gamma x t e,
    extend Gamma x t |- e \in t ->
    Gamma |- t \in star ->
    Gamma |- mu x t e \in t

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Ax" | Case_aux c "T_Var"
  | Case_aux c "T_App" | Case_aux c "T_Lam"
  | Case_aux c "T_Pi" | Case_aux c "T_CastUp"
  | Case_aux c "T_CastDown" | Case_aux c "T_Mu"].

Hint Constructors has_type.

Example typing_eg :
  extend empty y star |- app (abs x star (var x)) (var y) \in star.
Proof. apply (T_App _ x star star _ _); eauto. Qed.

(* Properties *)

Lemma canonical_form_lam : forall e y t1 t2,
  empty |- e \in (pi y t1 t2) ->
  value e ->
  exists x u, e = abs x t1 u.
Proof with eauto. intros. inversion H0; subst; try inversion H; subst...
  Case "CastUp" . inversion H; subst. inversion H7...
Qed.

Lemma canonical_form_castd : forall t e,
   empty |- castd e \in t ->
   value e ->
   exists t' e', e = castu t' e'.
Proof with eauto. intros. inversion H0; subst...
  Case "Star". inversion H; subst. inversion H2; subst. inversion H5.
  Case "Abs". inversion H; subst. inversion H2; subst. inversion H5.
  Case "Pi" . inversion H; subst. inversion H2; subst. inversion H5.
Qed.

(* Progress *)

Theorem progress : forall e t, empty |- e \in t -> value e \/ exists e', e => e'.
Proof with eauto.
  intros e t H.
  remember (@empty tm) as Gamma.
  has_type_cases (induction H) Case; subst Gamma...
  Case "T_Var". inversion H.
  Case "T_App".
    right. destruct IHhas_type1...
    SCase "e1 is a value".
      assert (exists x u, e1 = abs x t2 u).
      eapply canonical_form_lam...
      destruct H2 as [y0 [y1 Heq]]. subst.
      exists ([y0:=e2]y1)...
    SCase "e1 steps".
      inversion H1; subst...
  Case "T_CastDown".
    right. destruct IHhas_type1...
    SCase "e is a value".
      assert (exists t' e', e = castu t' e').
      eapply canonical_form_castd...
      destruct H3 as [t' [e' Heq]]. subst.
      exists e'...
    SCase "e steps".
      inversion H2; subst...
Qed.
