Require Import Coq.Lists.List.
Set Implicit Arguments.
Generalizable All Variables.
Local Open Scope list_scope.

CoInductive stream X := cons (x : X) (xs : stream X).

Fixpoint stream_nth {X} (ls : stream X) (n : nat) : X
  := match n, ls with
       | 0, cons x xs => x
       | S n', cons x xs => stream_nth xs n'
     end.

Fixpoint take {X} (n : nat) (ls : stream X) : list X
  := match n, ls with
       | 0, _ => nil
       | S n', cons x xs => x::take n' xs
     end.


Inductive BotResult := C | D.
Definition opposite_result (x : BotResult) : BotResult
  := match x with C => D | D => C end.

Inductive MBot :=
| MC
| MD
| MODAL_BASED_ON (tests : list ((*test_bot:*)MBot * (*on_bot:*) MBot))
                 (on_results : list BotResult -> BotResult)
| OtherMBot
| SelfMBot
| CompleteMBot (b : MBot)
| WaitMBot (b : MBot).

Fixpoint replace_self_other_with (with_self_b with_other_b in_b : MBot) : MBot
  := match in_b with
       | MC => MC
       | MD => MD
       | MODAL_BASED_ON tests f
         => MODAL_BASED_ON (List.map (fun b1b2 =>
                                        (replace_self_other_with with_self_b with_other_b (fst b1b2),
                                         replace_self_other_with with_self_b with_other_b (snd b1b2))) tests) f
       | OtherMBot => with_other_b
       | SelfMBot => with_self_b
       | CompleteMBot b' => CompleteMBot b'
       | WaitMBot b => WaitMBot (replace_self_other_with with_self_b with_other_b b)
     end.

Fixpoint fold_and_res (ls : list BotResult) : BotResult
  := match ls with
       | nil => C
       | C::xs => fold_and_res xs
       | D::_ => D
     end.

Delimit Scope mbot_scope with mbot.
Bind Scope mbot_scope with MBot.
Local Open Scope mbot_scope.

Definition MKripkeFrame'
           (MKripkeFrame : nat -> MBot -> MBot -> BotResult * BotResult)
           (frame_index : nat)
           (b1 : MBot) (b2 : MBot)
: BotResult * BotResult
  := match frame_index with
       | 0 => (C, C)
       | S n' =>
         (match b1 with
            | MC => C
            | MD => D
            | SelfMBot => fst (MKripkeFrame n' b1 b2)
            | OtherMBot => snd (MKripkeFrame n' b1 b2)
            | MODAL_BASED_ON ls f =>
              f (List.map
                   (fun b1b2 =>
                      fst (MKripkeFrame
                             n'
                             (replace_self_other_with b1 b2 (fst b1b2))
                             (replace_self_other_with b1 b2 (snd b1b2))))
                   ls)
            | CompleteMBot b => fst (MKripkeFrame n' (replace_self_other_with b1 b2 b) b2)
            | WaitMBot b => fst (MKripkeFrame n' (replace_self_other_with b1 b2 b) b2)
          end,
          match b2 with
            | MC => C
            | MD => D
            | SelfMBot => fst (MKripkeFrame n' b2 b1)
            | OtherMBot => snd (MKripkeFrame n' b2 b1)
            | MODAL_BASED_ON ls f =>
              f (List.map
                   (fun b1b2 =>
                      fst (MKripkeFrame
                             n'
                             (replace_self_other_with b2 b1 (fst b1b2))
                             (replace_self_other_with b2 b1 (snd b1b2))))
                   ls)
            | CompleteMBot b => fst (MKripkeFrame n' (replace_self_other_with b2 b1 b) b1)
            | WaitMBot b => fst (MKripkeFrame n' (replace_self_other_with b2 b1 b) b1)
          end)
     end.

Fixpoint MKripkeFrame (frame_index : nat) (b1 : MBot) (b2 : MBot)
: BotResult * BotResult
  := MKripkeFrame' MKripkeFrame frame_index b1 b2.

Lemma MKripkeFrame_sym
: forall n b1 b2,
    MKripkeFrame n b1 b2 = ((fun x => (snd x, fst x)) (MKripkeFrame n b2 b1)).
Proof.
  induction n; [ reflexivity | ].
  pose proof (fun b1 b2 => f_equal (@fst _ _) (IHn b1 b2)) as IHn'.
  simpl in IHn'.
  destruct b1, b2; simpl; try reflexivity; try rewrite IHn'; try reflexivity.
Qed.

CoFixpoint MKripkeFrames_from (n : nat) (b1 : MBot) (b2 : MBot) : stream (BotResult * BotResult)
  := cons (MKripkeFrame n b1 b2) (MKripkeFrames_from (S n) b1 b2).

Definition CooperateMBot : MBot := CompleteMBot MC.
Definition DefectMBot : MBot := CompleteMBot MD.
Definition OppositeMBotOf (b : MBot) : MBot := MODAL_BASED_ON
                                                 ((b, SelfMBot)::nil)
                                                 (fun res => opposite_result (fold_and_res res)).
Definition OppositeMBot := CompleteMBot (OppositeMBotOf OtherMBot).
Notation "B0 /\\ B1 /\\ .. /\\ Bn"
  := (MODAL_BASED_ON
        (Datatypes.cons B0%mbot (Datatypes.cons B1%mbot .. (Datatypes.cons Bn%mbot nil) .. ))
        fold_and_res)
       (at level 80, right associativity)
     : mbot_scope.

Notation CmB := CooperateMBot.
Notation DmB := DefectMBot.
Notation "~ B" := (OppositeMBotOf B) : mbot_scope.
Definition FairMBot : MBot := CompleteMBot OtherMBot.
Notation FmB := FairMBot.
Definition PrudentMBot : MBot := CompleteMBot (CompleteMBot ((OtherMBot, SelfMBot) /\\ (WaitMBot (~OtherMBot), DmB))).
Definition TrollMBot : MBot := CompleteMBot (MODAL_BASED_ON
                                               ((OtherMBot, DmB)::nil)
                                               (fun res => opposite_result (fold_and_res res))).

Definition IsEventually (b : MBot * MBot) (r : BotResult * BotResult)
  := exists n, forall m, MKripkeFrame (n + m) (fst b) (snd b) = r.

Definition IsEventually_fst (b : MBot * MBot) (r : BotResult)
  := exists n, forall m, fst (MKripkeFrame (n + m) (fst b) (snd b)) = r.

Definition IsUnexploitable (b : MBot)
  := forall b', ~IsEventually (b, b') (C, D).
Definition IsHappy (b : MBot)
  := IsEventually (b, b) (C, C).
Definition IsGood (b : MBot)
  := IsUnexploitable b /\ IsHappy b
     /\ IsEventually (b, PrudentMBot) (C, C)
     /\ IsEventually (b, FairMBot) (C, C).

Lemma CmB_C : forall b, IsEventually_fst (CmB, b) C.
Proof. intro b; exists 1; intro m; revert b; induction m; reflexivity. Qed.
Lemma DmB_D : forall b, IsEventually_fst (DmB, b) D.
Proof. intro b; exists 2; intro m; revert b; induction m; reflexivity. Qed.

Lemma Lob (b1 b2 : MBot)
: (forall m, MKripkeFrame m b1 b2 = (C, C) -> MKripkeFrame (S m) b1 b2 = (C, C))
  -> forall m, MKripkeFrame m b1 b2 = (C, C).
Proof.
  intro IH; induction m.
  { reflexivity. }
  { apply IH, IHm. }
Qed.

Lemma helper x y : (forall m, MKripkeFrame m x y = (C, C)) -> (forall m, (fst (MKripkeFrame m x y), fst (MKripkeFrame m x y)) = (C, C)).
Proof.
  intros H m; rewrite !H; reflexivity.
Qed.

Lemma FairMBot_Happy : IsHappy FairMBot.
Proof.
  exists 3; simpl.
  apply helper.
  induction m; simpl in *; trivial; rewrite IHm; reflexivity.
Qed.

Eval compute in MKripkeFrame 4 PrudentMBot PrudentMBot.
Eval compute in MKripkeFrame 4 PrudentMBot DmB.


(*Class ClassOfMBots := is_good_bot : MBot -> Prop.
Existing Class is_good_bot.
Class IsGoodClass (C : ClassOfMBots)
  := bot_result : forall b, `{is_good_bot b} -> stream MBotResult.
Arguments bot_result {C _} b {_}.

Definition action_on_frame `{@IsGoodClass cls} (b : MBot) {g : is_good_bot b}
         (frame_index : nat) : MBotResult
  := stream_nth (bot_result b _) frame_index.



(*| BASED_ON (test_bot : Bot) (on_bot : Bot)
           (using_results : stream BotResult -> Bot)
| BASED_ON_PREFIX_THEN (test_bot : Bot) (on_bot : Bot) (first_n : nat)
                       (using_results : list BotResult -> Bot)*)
*)
