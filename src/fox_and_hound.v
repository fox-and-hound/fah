Require Import ClassicalExtras.
Require Import MyNotation.
Require Import Setoid.
Require Import FunctionalExtensionality.

Require Import Galois.
Require Import LanguageModel.
Require Import TraceModel.
Require Import Properties.
Require Import ChainModel.
Require Import RobustTraceProperty.

Require Import RobustHyperProperty.

Set Implicit Arguments.
Unset Printing Implicit Defensive.


Section FoxAndHound.
  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  (*CA: we don't need a particular structure of traces to define preservation
        e.g. traces = values or our defn of traces both make sense
   *)
  Variable trace__S trace__T : Type.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.
  Local Definition hprop__S := hprop trace__S.
  Local Definition hprop__T := hprop trace__T.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition beh__S := beh Source_Semantics.
  Local Definition beh__T := beh Target_Semantics.
  Local Definition par__S := par Source.
  Local Definition par__T := par Target.
  Local Definition ctx__S := ctx Source.
  Local Definition ctx__T := ctx Target.
  Local Definition rhsat__S := rhsat Source_Semantics.
  Local Definition rhsat__T := rhsat Target_Semantics.

  Local Definition hempty__S : hprop__S := fun _ => False.
  Local Definition hempty__T : hprop__T := fun _ => False.

  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
  (* CA: don't understand why this does not work *)
  Local Notation "C [ P ]" := (plug _  P C) (at level 50).
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  (* I don't like very much this way of formalizing equality of behaviors, but it seems the easiest one. *)
  Local Definition eq__S (P1 P2 : par__S) := forall C__S, beh__S (C__S [P1]) = beh__S (C__S [P2]).
  Local Definition eq__T (P1 P2 : par__T) := forall C__T, beh__T (C__T [P1]) = beh__T (C__T [P2]).

  Definition pres_beq := forall P1 P2, eq__S P1 P2 -> eq__T (P1↓) (P2↓).
  Definition refl_beq := forall P1 P2, eq__T (P1↓) (P2↓) -> eq__S P1 P2.
  Definition FAC := pres_beq /\ refl_beq.

  (** TODO: RHP__τ, I don't know how to use the current τRhP/τRHP since τ seems to be fixed beforehand. *)
  Definition RHPτ (τ : hprop__S -> hprop__T) := forall P H__S, (rhsat__S P H__S -> rhsat__T (P ↓) (τ H__S)).
  Definition minimal__T (τ : hprop__S -> hprop__T) := forall (α : hprop__S -> hprop__T),
      RHPτ α -> (forall H__S, (τ H__S) ⊆ (α H__S)). 

  Definition RHPσ (σ : hprop__T -> hprop__S) := forall P H__T, (rhsat__S P (σ H__T) -> rhsat__T (P ↓) H__T).
  Definition maximal__S (σ : hprop__T -> hprop__S) := forall (β : hprop__T -> hprop__S),
      RHPσ β -> (forall H__T, (β H__T) ⊆ (σ H__T)).


  
  (** TODO:  would be nicer to have the compiler as a parameter, but then should change all the defs *)
  (* Also, this uses FunctionalExtensionality! *)
  (*CA: well, only if you want to prove it, you may need functional
  extensionality. You can state it without f.ext. *)
  Definition R__cmp (f__S : ctx__S -> prop__S) (g__T : ctx__T -> prop__T) : Prop :=
    exists P, f__S = (fun C__S => beh__S (C__S[P])) /\ g__T = (fun C__T => beh__T (C__T[P↓])).
  
  Lemma funct_lemma : pres_beq ->
                       (forall f__S g__T g'__T, R__cmp f__S g__T /\ R__cmp f__S g'__T -> g__T = g'__T).
  Proof.
    unfold pres_beq, R__cmp.
    intros pres f__S g__T g'__T [[P [H0eqf__S H0eqg__T]] [P' [H1eqf__S H1eqg__T]]].
    rewrite H0eqf__S in H1eqf__S.
    assert (Heq__S : eq__S P P') by (unfold eq__S; intro C__S; apply (equal_f H1eqf__S)).
    apply (pres P P') in Heq__S.
    unfold eq__T in Heq__S.
    extensionality in Heq__S.
    rewrite H0eqg__T. rewrite H1eqg__T.
    assumption.
  Qed.

  (* CA: this does not match exactly the paper but it's ok *)
  Definition R__fun (Hpres : pres_beq) (P : par__S) :
     { g | R__cmp (fun C__S => beh__S (C__S [P])) g }.
  Proof.
   exists (fun C__T => beh__T (C__T [P ↓])). 
   now exists P.
  Defined.   
 
  
  (* CA: This would be the injectivity part  *)
  Lemma funct_lemma' : refl_beq ->
                       (forall f f' g, R__cmp f g /\ R__cmp f' g -> f = f').
  Proof.
    unfold refl_beq, R__cmp.
    intros refl f f' g [[P [Heqf Heqg]] [P' [Heqf' Heqg']]].
    rewrite Heqf, Heqf'.
    apply functional_extensionality. 
    apply (refl P P').
    intro C__T.
    assert (Hfoo : (g C__T) = (beh__T (C__T [P ↓]))) by now rewrite Heqg.  
    assert (Hfoo' : (g C__T) = (beh__T (C__T [P' ↓]))) by now rewrite Heqg'.
    now rewrite <- Hfoo, <- Hfoo'.  
  Qed. 

  Definition R__fun' (Hrefl : refl_beq) (P : par__S) :
    {f | R__cmp f (fun C__T => beh__T (C__T [P↓])) }. 
  Proof.
    exists (fun C__S => beh__S (C__S [P])). 
    now exists P.
  Defined.
  
  (* Lemma inj_lemma : FAC -> *)
  (*                   (forall f__S f'__S P1 P2, *)
  (*                       f__S = (fun C__S => beh__S (C__S[P1])) -> f'__S = (fun C__S => beh__S (C__S[P2])) -> *)
  (*                       (R__cmp f__S = R__cmp f'__S) -> f__S = f'__S). *)
  (* Proof. *)
    
    
  (*   intros [Hpres Hrefl] fs fs' P1 P2 Hfs1 Hfs2 Req. *)
  (*   rewrite Hfs1, Hfs2. *)
  (*   apply functional_extensionality. *)
  (*   intro C__S. *)
    
  (*   unfold FAC. *)
  (*   intros [Hpres_beq Hrefl_beq]. *)
  (*   (* We could avoid this, but I like it more this way so we need the contrapositive of reflection and injection *) *)
  (*   assert (Hrefl_contra: refl_beq <-> (forall P1 P2, not(eq__S P1 P2) -> not(eq__T (P1↓) (P2↓)))). *)
  (*   { *)
  (*     split. *)
  (*     - auto. *)
  (*     - unfold refl_beq. intros refl_contra P1 P2 Heq__T. specialize (refl_contra P1 P2). rewrite contra in refl_contra. apply NNPP in refl_contra. assumption. apply PNNP. assumption. *)
  (*   } *)
  (*   rewrite Hrefl_contra in Hrefl_beq. *)
  (*   clear Hrefl_contra. *)

  (*   intros f__S f'__S P1 P2 [Df__S Df'__S]. *)
  (*   assert (inj_contra : (R__cmp f__S = R__cmp f'__S -> f__S = f'__S) <-> (f__S <> f'__S -> R__cmp f__S <> R__cmp f'__S)) by (apply contra). *)
  (*   rewrite inj_contra.  *)
  (*   clear inj_contra. *)

  (*   intro Hneq. *)

  (*   assert (HnbehS : exists C__S, beh__S (C__S[P1]) <> beh__S (C__S[P2])). *)
  (*   { *)
  (*     specialize (functional_extensionality f__S f'__S). *)
  (*     intro Hfne. *)
  (*     apply contra in Hfne. *)
  (*     - apply not_all_ex_not in Hfne. rewrite Df__S, Df'__S in Hfne. apply Hfne. *)
  (*     - assumption. *)
  (*   } *)

  (*   unfold eq__S in Hrefl_beq. *)
  (*   specialize (Hrefl_beq P1 P2). *)
  (*   apply ex_not_not_all in HnbehS. *)
  (*   specialize (Hrefl_beq HnbehS). *)
  (* Admitted. *)

  (* Local Definition eq_H_g (H__T : hprop__T) (g__T : ctx__T -> prop__T) := *)
  (*   forall π, (exists C__T, π = g__T C__T) <-> H__T π. *)

  (* Definition τ__min (H__S : hprop__S) (H__T : hprop__T) := *) (*
  let f := fun P C__S => beh__S(C__S [P]) in *) (* (exists P, rhsat__S
  P H__S /\ (forall g__T, R__cmp (f P) g__T -> eq_H_g H__T g__T)) \/
  (H__T = hempty__T).  *)

  (* (* from g : ctx -> prop to an hyperproperty *) *)
  (* Definition g2H (g : ctx__T -> prop__T) : hprop__T := *)
  (*   fun π => exists C__T, (g C__T) = π.  *)

  (* (*from a program to f : ctx -> Prop *) *)
  (* Definition fP (P : par__S): ctx__S-> prop__S := *)
  (*   fun C__S => beh__S (C__S [P]).  *)


  Definition τfun { Hpres : pres_beq } : hprop__S -> hprop__T.
  Proof.
   intros H__S.
   exact (fun π__T => exists P C__T, (rhsat__S P H__S) /\ (π__T = (proj1_sig (R__fun Hpres P)) C__T)).
  Defined.
  
  Theorem FAC_imply_RHPτ : FAC -> exists τ, RHPτ τ /\ minimal__T τ. 
  Proof.
    intros [Hpres Hrefl].
    exists (@τfun Hpres).
    split.
    - intros P H__S Hrsat C__T.
      unfold hsat, τfun. 
      now exists P, C__T.
    - intros α α_RHP H__S π__T.
      unfold τfun.
      intros [P1 [C__T1 [H1 Heq]]].
      rewrite Heq.
      now apply α_RHP. 
  Qed.

  (* Definition σfun { Hrefl : refl_beq } : hprop__T -> hprop__S. *)
  (* Proof. *)
  (*  intros H__T. *)
  (*  exact (fun π__S => forall P C__T, (exists C__S,  (π__S = proj1_sig (R__fun' Hrefl P) C__S)) -> *)
  (*                                   H__T (beh__T (C__T [P ↓]))). *)
  (* Defined. *)

  Definition σfun { Hrefl : refl_beq } { Hpres : pres_beq }  : hprop__T -> hprop__S.
  Proof.
   intros H__T.
   exact (fun π__S => (forall C__S P,  π__S = proj1_sig (R__fun' Hrefl P) C__S ->
                         rhsat__T (P↓) H__T )).
  Defined.


  Variable aC__S : ctx__S. 
  
  Lemma Gfst { Hpres : pres_beq } { Hrefl : refl_beq } :
    forall H__T : hprop__T, (@τfun Hpres) (@σfun Hrefl Hpres H__T) ⊆ H__T. 
  Proof.
    intro H__T.
    unfold τfun, σfun.
    intros π__T [P [C__T [H1 H2]]]. simpl in *.
    subst.
    specialize (H1 aC__S aC__S P).
    now apply H1.   
  Qed.

  Lemma Gsnd { Hpres : pres_beq } { Hrefl : refl_beq } :
    forall H__S : hprop__S, H__S ⊆ ((@σfun Hrefl Hpres) (@τfun Hpres H__S)).
  Proof.
    intros H__S π__S Hπ.
    unfold σfun, τfun. simpl. 
    intros C__S P Heq C__T.
    unfold hsat. 
    exists P, C__T.
    split; auto.
  Abort. (*we don't know rhsat P H__S *)
  (*CA: σ is not the adjoint of τ... Does τ have an adjoint? 
        if so pick that as σ and get the following equivalence.
   *)
    
    
  Lemma στRHP { Hpres : pres_beq } { Hrefl : refl_beq } :
    (RHPσ (@σfun Hrefl Hpres) <-> RHPτ (@τfun Hpres)).
  Proof.
    split.
    - admit. (* CA: probably not true *)      
    - intros Hτ P H__T Hsrc C__T.
      specialize (Hτ P (@σfun Hrefl Hpres H__T) Hsrc C__T).
      unfold hsat in *.
      eapply hsat_upper_closed.
      exact Hτ. 
      apply Gfst.
   Admitted. 
  
  
  Theorem FAC_imply_RHPσ : FAC -> exists σ, RHPσ σ /\ maximal__S σ. 
  Proof.
    intros [Hpres Hrefl].
    exists (@σfun Hrefl Hpres).
    split.
    - admit. (*CA: consequence of στRHP "<="*)
    - Admitted. (* not sure this is true... It's probably better to jsut show  στRHP *)

  
Section NoFAC.

  (* In principle one can always define the following function τ, and
     show that every compiler is RHPτ w.r.t τ, and that it is minimal
     with such a property.

     Notice however that being able to compute τfun below means know
     the exact behavior of P↓ in an arbitrary target context, hence
     much more than knowing which hyperproperty is robustly satisfied
     after compilation.

  *)
  
  Definition τfun' : hprop__S -> hprop__T.
  Proof.
    intro H__S.
    unfold hprop__T, hprop.
    exact (fun π__T => exists P C__T, (rhsat__S P H__S) /\ (π__T = beh__T (C__T [P ↓] ) )).
  Defined.

  (*CA: FAC never used! *)                
  Theorem FAC_imply_RHPτ' : exists τ, RHPτ τ /\ minimal__T τ. 
  Proof.
    (* intros [Hpres Hrefl]. *)
    exists τfun'.
    split.
    - intros P H__S Hrsat C__T.
      unfold hsat, τfun'. 
      now exists P, C__T.
    - intros α α_RHP H__S π__T.
      unfold τfun'.
      intros [P1 [C__T1 [H1 Heq]]].
      rewrite Heq.
      now apply α_RHP. 
  Qed.

End NoFAC.
  
End FoxAndHound.
