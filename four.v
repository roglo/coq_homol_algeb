(* WORK IN PROGRESS (2018-05-30) *)

(* The two Four Lemmas *)

Require Import Utf8.
Require Import AbGroup Setoid.

Theorem epi_is_surj : ∀ D D' (d : HomGr D D'),
  Decidable_Equality * Excluded_Middle
  → is_epi d
  → ∀ t', t' ∈ D' → ∃ t, t ∈ D ∧ (Happ d t = t')%G.
Proof.
intros * (eq_dec, excl_midd) Hed * Ht'.
assert (Hn : ¬ (∀ t, t ∈ D → (Happ d t ≠ t')%G)). {
(*
  set (v t'₁ := (t'₁ : gr_set (Coker d))).
*)
  (* trick to make identity of type gr_set D' → gr_set (Coker d) *)
  set (v t'₁ := (if eq_dec _ t'₁ t' then t'₁ else t'₁) : gr_set (Coker d)).
(**)
  assert (Hvid : ∀ x, v x = x). {
    intros; unfold v.
    now destruct (eq_dec _ x t').
  }
  assert (Hmc : ∀ t, t ∈ D' → v t ∈ D'). {
    intros t Ht; now rewrite Hvid.
  }
  assert (Hac : ∀ x y, x ∈ D' → y ∈ D' → (x = y)%G → (v x = v y)%G). {
    intros * Hx Hy Hxy.
    do 2 rewrite Hvid.
    simpl; unfold Coker_eq; simpl.
    exists 0; split; [ apply D | now rewrite Hzero, Hxy, gr_add_inv_r ].
  }
  assert (Had : ∀ x y, x ∈ D' → y ∈ D' → (v (x + y) = v x + v y)%G). {
    intros * Hx Hy.
    do 3 rewrite Hvid.
    exists 0; split; [ apply D | now rewrite Hzero, gr_add_inv_r ].
  }
  set (hv :=
    {| Happ := v;
       Hmem_compat := Hmc;
       Happ_compat := Hac;
       Hadditive := Had |}).

...
  set (w (d' : gr_set D') := false).
  specialize (Hed (Coker d)) as H1.
...
  specialize (Hed _ v w) as H1.
  intros H2.
  assert (H : ∀ t, t ∈ D → v (Happ d t) = w (Happ d t)). {
    intros t Ht.
    unfold v, w.
    destruct (eq_dec _ (Happ d t) t') as [H| H]; [ | easy ].
    now specialize (H2 t Ht).
  }
  specialize (H1 H t' Ht'); clear H.
  unfold v, w in H1.
  destruct (eq_dec _ t' t') as [H3| H3]; [ easy | ].
  now apply H3.
}
specialize (excl_midd (∃ t, t ∈ D ∧ (Happ d t = t')%G)) as H2.
destruct H2 as [H2| H2]; [ easy | ].
exfalso; apply Hn; intros t Ht H3.
apply H2.
now exists t.
Qed.

(* Four lemma #1
           g       h        j
        B------>C------>D------>E
        |       |       |       Γ
       b|      c|      d|      e|
        v       |       v       |
        v       v       v       v
        B'----->C'----->D'----->E'
           g'      h'      j'

  If 1/ the diagram is commutative,
     2/ (g, h, j) and (g', h', j') are exact,
     3/ b and d are epimorphisms,
     4/ e is monomorphism,
  Then
     c is an epimorphism.
*)

Lemma four_1 :
  ∀ (B C D E B' C' D' E' : AbGroup)
     (g : HomGr B C) (h : HomGr C D) (j : HomGr D E)
     (g' : HomGr B' C') (h' : HomGr C' D') (j' : HomGr D' E')
     (b : HomGr B B') (c : HomGr C C')
     (d : HomGr D D') (e : HomGr E E'),
  (Decidable_Equality * Excluded_Middle)
  → diagram_commutes g b c g'
  → diagram_commutes h c d h'
  → diagram_commutes j d e j'
  → exact_sequence [g; h; j]
  → exact_sequence [g'; h'; j']
  → is_epi b ∧ is_epi d ∧ is_mono e
  → is_epi c.
Proof.
intros * (eq_dec, excl_midd) Hcgg' Hchh' Hcjj' s s' (Heb & Hed & Hme).
unfold is_epi.
enough
  (∀ T (g₁ g₂ : gr_set C' → T),
  (∀ z, z ∈ C → g₁ (Happ c z) = g₂ (Happ c z))
  → ∀ z', z' ∈ C' → g₁ z' = g₂ z'). {
  now intros T g₁ g₂ H1; apply H.
}
intros * Hgc * Hz'.
assert (H : ∃ t, t ∈ D ∧ (Happ d t = Happ h' z')%G). {
apply epi_is_surj; [ easy | easy | now apply h' ].
}
destruct H as (t & Ht & Hdt).
move t after z'; move Ht after Hz'.
assert (H : ∃ z, z ∈ C ∧ (Happ h z = t)%G). {
  assert (H : t ∈ Ker j). {
    split; [ easy | ].
    assert (H : (Happ e (Happ j t) = 0)%G). {
      rewrite Hcjj'.
      etransitivity.
      -apply Happ_compat; [ now apply d | | apply Hdt ].
       now apply h'.
      -assert (H : Happ h' z' ∈ Im h') by (exists z'; easy).
       now apply s' in H; simpl in H.
    }
    specialize (Hme bool (λ b, if b then Happ j t else 0) (λ _, 0)) as H1.
    simpl in H1.
    assert
      (H2 : ∀ x : bool, (Happ e (if x then Happ j t else 0) = Happ e 0)%G). {
      intros x; destruct x; [ | easy ].
      now rewrite Hzero.
    }
    now specialize (H1 H2 true); clear H2.
  }
  apply s in H.
  destruct H as (z & Hz & Hhz).
  now exists z.
}
destruct H as (z & Hz & Hhz).
move z after t; move Hz after Ht.
assert (H : Happ c z - z' ∈ Ker h'). {
  split.
  -apply C'; [ now apply c | now apply C' ].
  -rewrite Hadditive; [ | now apply c | now apply C' ].
   rewrite Hinv; [ | easy ].
   rewrite <- Hchh'.
   apply gr_sub_move_r.
   rewrite gr_add_0_l.
   etransitivity; [ | apply Hdt ].
   apply d; [ now apply h | easy | apply Hhz ].
}
apply s' in H.
destruct H as (y' & Hy' & Hgy').
move y' after z'; move Hy' before Hz'.
assert (H : ∃ y, y ∈ B ∧ (Happ b y = y')%G) by now apply epi_is_surj.
destruct H as (y & Hy & Hby).
move y after z; move Hy before Hz.
specialize (Hgc (z - Happ g y)) as H1.
assert (H : z - Happ g y ∈ C). {
  apply C; [ easy | now apply C, g ].
}
specialize (H1 H); clear H.
assert (H : (Happ c (z - Happ g y) = z')%G). {
  rewrite Hadditive; [ | easy | now apply C, g ].
  rewrite Hinv; [ | now apply g ].
  apply gr_sub_move_r.
  apply gr_sub_move_l.
  rewrite <- Hgy'.
  rewrite Hcgg'.
  apply g'; [ easy | now apply b | ].
  now symmetry.
}
(* rats! g₁ and g₂ must be morphisms,
   I must change the definition of is_epi *)
...
