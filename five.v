(* WORK IN PROGRESS (2018-05-18) *)

(* Five lemma *)

Require Import Utf8.
Require Import AbGroup Setoid.

Definition is_mono {A B} (f : HomGr A B) :=
  ∀ C (g₁ g₂ : C → gr_set A),
  (∀ x, (Happ f (g₁ x) = Happ f (g₂ x))%G)
  → (∀ x, (g₁ x = g₂ x)%G).

Definition is_epi {A B} (f : HomGr A B) :=
  ∀ C (g₁ g₂ : gr_set B → C),
  (∀ x, g₁ (Happ f x) = g₂ (Happ f x))
  → (∀ y, g₁ y = g₂ y).

Definition is_iso {A B} (f : HomGr A B) :=
  ∃ g : HomGr B A,
  (∀ x, (Happ g (Happ f x) = x)%G) ∧
  (∀ y, (Happ f (Happ g y) = y)%G).

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
  (H1 : ∀ x', ∃ x, x' ∈ C' → x ∈ C ∧ (Happ h x = Happ d₁ (Happ h' x'))%G). {
  intros x'.
  destruct (MemDec C' x') as [Hx'| Hx'].
  -set (y := Happ j (Happ d₁ (Happ h' x'))).
   assert (H : y ∈ Ker e). {
     split; [ now apply j, d₁, h' | ].
     unfold y; rewrite Hcjj'.
     etransitivity.
     -apply j'; [ now apply d, d₁, h' | | apply Hdd₁ ].
      now apply h'.
     -assert (H : Happ h' x' ∈ Ker j') by now apply s'; exists x'.
      now simpl in H.
   }
   destruct H as (Hj & Hej).
   specialize (Hme bool (λ b, if b then 0 else y) (λ _, 0)) as H1.
   simpl in Hme.
   assert (H : ∀ x : bool, (Happ e (if x then 0 else y) = Happ e 0)%G). {
     intros.
     destruct x; [ easy | now rewrite Hej, Hzero ].
   }
   specialize (H1 H); clear H.
   simpl in H1.
   specialize (H1 false); simpl in H1.
   assert (H2 : Happ d₁ (Happ h' x') ∈ Ker j). {
     split; [ now apply d₁, h' | easy ].
   }
   apply s in H2.
   destruct H2 as (x & Hx & Hhx).
   exists x; intros Hx'2; easy.
  -exists 0; intros; easy.
}
specialize (Function_of_Relation H1) as (cf₁, Hc₁).
clear H1.
assert (cmem_compat : ∀ x : gr_set C', x ∈ C' → cf₁ x ∈ C). {
  intros * Hx.
  now apply Hc₁.
}
assert
  (capp_compat :
   ∀ x y : gr_set C', x ∈ C' → y ∈ C' → (x = y)%G → (cf₁ x = cf₁ y)%G). {
  intros * Hx Hy Hxy.
  specialize (Hc₁ x Hx) as H; destruct H as (Hcx, Hhx).
  specialize (Hc₁ y Hy) as H; destruct H as (Hcy, Hhy).
  move Hcy before Hcx.
...
  assert (Hc₁x : cf₁ x ∈ C) by now apply Hc₁.
  assert (Hc₁y : cf₁ y ∈ C) by now apply Hc₁.
  specialize (Happ_compat _ _ h (cf₁ x) (cf₁ y) Hc₁x Hc₁y) as H1.
    apply Hc₁.
...
}
assert (cadditive : ∀ x y : gr_set C', x ∈ C' → y ∈ C' → (cf₁ (x + y) = cf₁ x + cf₁ y)%G). ...
set
  (c₁ :=
     {| Happ := cf₁; Hmem_compat := cmem_compat; Happ_compat := capp_compat;
        Hadditive := cadditive |}).
...
