(* WORK IN PROGRESS (2018-05-18) *)

(* Five lemma *)

Require Import Utf8.
Require Import AbGroup Setoid.

(* Composition of homomorphims *)

Theorem comp_mem_compat {A B C} (f : HomGr A B) (g : HomGr B C) :
  ∀ x : gr_set A, x ∈ A → Happ g (Happ f x) ∈ C.
Proof.
intros x Hx.
now apply g, f.
Qed.

Theorem comp_app_compat {A B C} (f : HomGr A B) (g : HomGr B C) :
  ∀ x y : gr_set A,
  x ∈ A → y ∈ A → (x = y)%G → (Happ g (Happ f x) = Happ g (Happ f y))%G.
Proof.
intros * Hx Hy Hxy.
apply Happ_compat; now apply f.
Qed.

Theorem comp_additive {A B C} (f : HomGr A B) (g : HomGr B C) :
  ∀ x y : gr_set A,
  x ∈ A
  → y ∈ A
  → (Happ g (Happ f (x + y)) = Happ g (Happ f x) + Happ g (Happ f y))%G.
Proof.
intros * Hx Hy.
rewrite <- Hadditive; [ | now apply f | now apply f ].
apply g; [ now apply f, A | now apply B; apply f | now apply Hadditive ].
Qed.

Definition Hcomp {A B C} (g : HomGr B C) (f : HomGr A B) :=
  {| Happ x := Happ g (Happ f x);
     Hmem_compat := comp_mem_compat f g;
     Happ_compat := comp_app_compat f g;
     Hadditive := comp_additive f g |}.

(* The five lemma
         f      g       h        j
     A------>B------>C------>D------>E
     |       |       |       |       |
    a|      b|      c|      d|      e|
     |       |       |       |       |
     v       v       v       v       v
     A'----->B'----->C'----->D'----->E'
        f'      g'      h'      j'

  If 1/ the diagram is commutative,
     2/ (f, g, h, j) and (f', g', h', j') are exact
     3/ b and d are isomorphisms
     4/ a is an epimorphism
     5/ e is a monomorphism
  Then
     c is an isomorphism.
*)

Lemma five :
  ∀ (A B C D E A' B' C' D' E' : AbGroup)
     (f : HomGr A B) (g : HomGr B C) (h : HomGr C D) (j : HomGr D E)
     (f' : HomGr A' B') (g' : HomGr B' C')
     (h' : HomGr C' D') (j' : HomGr D' E')
     (a : HomGr A A') (b : HomGr B B') (c : HomGr C C')
     (d : HomGr D D') (e : HomGr E E'),
  diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → diagram_commutes h c d h'
  → diagram_commutes j d e j'
  → exact_sequence [f; g; h; j]
  → exact_sequence [f'; g'; h'; j']
  → is_epi a ∧ is_iso b ∧ is_iso d ∧ is_mono e
  → is_iso c.
Proof.
intros * Hcff' Hcgg' Hchh' Hcjj' s s' (Hea & Hib & Hid & Hme).
destruct Hib as (b₁ & Hb₁b & Hbb₁).
destruct Hid as (d₁ & Hd₁d & Hdd₁).
move b₁ before s'; move d₁ before b₁.
unfold is_iso.
enough
  (H : ∃ c₁,
   (∀ x : gr_set C, (Happ c₁ (Happ c x) = x)%G) ∧
   (∀ y : gr_set C', (Happ c (Happ c₁ y) = y)%G)). {
  destruct H as (c' & Hc'c & Hcc').
  now exists c'.
}
assert
  (H1 : ∀ z', ∃ z, z' ∈ C' → z ∈ C ∧ (Happ h z = Happ d₁ (Happ h' z'))%G). {
  intros z'.
  destruct (MemDec C' z') as [Hz'| Hz']; [ | now exists 0 ].
  set (u := Happ j (Happ d₁ (Happ h' z'))).
  assert (H : u ∈ Ker e). {
    split; [ now apply j, d₁, h' | ].
    unfold u; rewrite Hcjj'.
    etransitivity.
    -apply j'; [ now apply d, d₁, h' | | apply Hdd₁ ].
     now apply h'.
    -assert (H : Happ h' z' ∈ Ker j') by now apply s'; exists z'.
     now simpl in H.
  }
  destruct H as (Hj & Hej).
  specialize (Hme bool (λ b, if b then 0 else u) (λ _, 0)) as H1.
  simpl in Hme.
  assert (H : ∀ x : bool, (Happ e (if x then 0 else u) = Happ e 0)%G). {
    intros.
    destruct x; [ easy | now rewrite Hej, Hzero ].
  }
  specialize (H1 H); clear H.
  simpl in H1.
  specialize (H1 false); simpl in H1.
  assert (H2 : Happ d₁ (Happ h' z') ∈ Ker j). {
    split; [ now apply d₁, h' | easy ].
  }
  apply s in H2.
  destruct H2 as (z & Hz & Hhz).
  exists z; intros Hz'2; easy.
}
specialize (Function_of_Relation H1) as (fc₁, Hc₁).
clear H1.
assert (Hzy : ∀ z', z' ∈ C' → ∃ y', (Happ g' y' = z' - Happ c (fc₁ z'))%G). {
  intros z' Hz'.
  assert (H : z' - Happ c (fc₁ z') ∈ Ker h'). {
    split.
    -apply C'; [ easy | now apply C', c, Hc₁ ].
    -rewrite Hadditive; [ | easy | now apply C', c, Hc₁ ].
     rewrite Hinv; [ | now apply c, Hc₁ ].
     apply gr_sub_move_r; rewrite gr_add_0_l.
     rewrite <- Hchh'.
     symmetry.
     etransitivity; [ | apply Hdd₁ ].
     apply d; [ | apply d₁, h', Hz' | now apply Hc₁ ].
     now apply h, Hc₁.
  }
  apply s' in H.
  destruct H as (y' & Hy' & Hgy').
  now exists y'.
}
assert (Hzz1 : ∀ z', (Happ c (fc₁ z') = z')%G). {
  intros z'.
...
assert (cmem_compat : ∀ z' : gr_set C', z' ∈ C' → fc₁ z' ∈ C). {
  intros * Hz'.
  now apply Hc₁.
}
assert
  (capp_compat :
   ∀ z'1 z'2 : gr_set C', z'1 ∈ C' → z'2 ∈ C'
   → (z'1 = z'2)%G → (fc₁ z'1 = fc₁ z'2)%G). {
  intros * Hz'1 Hz'2 Hzz.
  specialize (Hc₁ z'1 Hz'1) as H; destruct H as (Hcz'1, Hhz'1).
  specialize (Hc₁ z'2 Hz'2) as H; destruct H as (Hcz'2, Hhz'2).
  move Hcz'2 before Hcz'1.
  assert (H1 : (Happ d₁ (Happ h' z'1) = Happ d₁ (Happ h' z'2))%G). {
    now apply d₁; apply h'.
  }
  rewrite <- Hhz'1, <- Hhz'2 in H1.
  assert (H2 : fc₁ z'1 - fc₁ z'2 ∈ Ker h). {
    split.
    -apply C; [ easy | now apply C ].
    -rewrite Hadditive; [ | easy | now apply C ].
     rewrite H1, Hinv; [ | easy ].
     apply gr_add_inv_r.
  }
  apply s in H2; destruct H2 as (y & Hy & Hgy).
...
}
assert (cadditive : ∀ z'1 z'2, z'1 ∈ C' → z'2 ∈ C' → (fc₁ (z'1 + z'2) = fc₁ z'1 + fc₁ z'2)%G).
 ...
set
  (c₁ :=
     {| Happ := fc₁; Hmem_compat := cmem_compat; Happ_compat := capp_compat;
        Hadditive := cadditive |}).
...
