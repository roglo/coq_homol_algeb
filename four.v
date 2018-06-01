(* WORK IN PROGRESS (2018-05-30) *)

(* The two Four Lemmas *)

Require Import Utf8.
Require Import AbGroup Setoid.

Theorem epi_is_surj : ∀ A B (f : HomGr A B),
  is_epi f
  → ∀ y, y ∈ B → ∃ t, t ∈ A ∧ (Happ f t = y)%G.
Proof.
intros * Hed y Hy.
(* trick to make identity of type gr_set B → gr_set (Coker f) *)
set (v y1 := let _ := gr_mem B y1 in y1 : gr_set (Coker f)).
assert (Hmc : ∀ y1, y1 ∈ B → v y1 ∈ B) by easy.
assert (Hac : ∀ y1 y2, y1 ∈ B → y2 ∈ B → (y1 = y2)%G → (v y1 = v y2)%G). {
  intros * Hy1 Hy2 Hyy.
  exists 0; split; [ apply A | ].
  now unfold v; simpl; rewrite Hzero, Hyy, gr_add_inv_r.
}
assert (Had : ∀ y1 y2, y1 ∈ B → y2 ∈ B → (v (y1 + y2) = v y1 + v y2)%G). {
  intros * Hy1 Hy2.
  exists 0; split; [ apply A | now unfold v; rewrite Hzero, gr_add_inv_r ].
}
set (hv :=
  {| Happ := v;
     Hmem_compat := Hmc;
     Happ_compat := Hac;
     Hadditive := Had |}).
assert (Hmc₀ : ∀ y1, y1 ∈ B → 0 ∈ Coker f) by (intros; apply B).
assert
  (Hac₀ :
   ∀ y1 y2, y1 ∈ B → y2 ∈ B→ (y1 = y2)%G → (@gr_zero (Coker f) = 0)%G). {
  intros * Hy1 Hy2 Hyy.
  simpl; unfold Coker_eq; simpl.
  exists 0; split; [ apply A | now rewrite Hzero, gr_add_inv_r ].
}
assert (Had₀ : ∀ y1 y2, y1 ∈ B → y2 ∈ B → (@gr_zero (Coker f) = 0 + 0)%G). {
  intros * Hy1 Hy2.
  simpl; unfold Coker_eq; simpl.
  exists 0; split; [ apply A | now rewrite Hzero, gr_add_0_r, gr_sub_0_r ].
}
set (hw :=
  {| Happ _ := 0;
     Hmem_compat := Hmc₀;
     Happ_compat := Hac₀;
     Hadditive := Had₀ |}).
specialize (Hed (Coker f) hv hw) as H1.
assert (H : ∀ x, x ∈ A → (Happ hv (Happ f x) = Happ hw (Happ f x))%G). {
  intros x Hx.
  simpl; unfold v; unfold Coker_eq; simpl.
  exists x; split; [ easy | now rewrite gr_sub_0_r ].
}
specialize (H1 H y Hy); clear H.
simpl in H1; unfold Coker_eq in H1; simpl in H1.
destruct H1 as (x & Hx).
rewrite gr_sub_0_r in Hx.
now exists x.
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
  diagram_commutes g b c g'
  → diagram_commutes h c d h'
  → diagram_commutes j d e j'
  → exact_sequence [g; h; j]
  → exact_sequence [g'; h'; j']
  → is_epi b ∧ is_epi d ∧ is_mono e
  → is_epi c.
Proof.
intros * Hcgg' Hchh' Hcjj' s s' (Heb & Hed & Hme).
unfold is_epi.
enough
  (∀ T (g₁ g₂ : HomGr C' T),
   (∀ z, z ∈ C → (Happ g₁ (Happ c z) = Happ g₂ (Happ c z))%G)
   → ∀ z', z' ∈ C' → (Happ g₁ z' = Happ g₂ z')%G). {
  now intros T g₁ g₂ H1; apply H.
}
intros * Hgc * Hz'.
assert (H : ∃ t, t ∈ D ∧ (Happ d t = Happ h' z')%G). {
  apply epi_is_surj; [ easy | now apply h' ].
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
...
