(* Abelian groups and Homomorphisms *)

Require Import Utf8.
Require Import Setoid.

Reserved Notation "x '∈' S" (at level 60).
Reserved Notation "x '≡' y" (at level 70).

(* Abelian Groups.

   Notes:

   -sets in groups are predicates (naive theory of sets); a value of type
    gr_set is not necessarily in the group set. To be in the group set, it
    must satisfy the predicate gr_mem, which is later syntaxified by the
    usual symbol ∈.

   -group sets are setoids: there is a specific equality (gr_eq) which is
    compatible with membership (gr_mem_compat), addition (gr_add_compat),
    and inverse (gr_inv_compat). This allows to define quotient groups,
    for example in cokernets, by changing this equality.
*)

Record AbGroup :=
  { (* data *)
    gr_set : Type;
    gr_mem : gr_set → Prop where "x ∈ G" := (gr_mem x);
    gr_eq : gr_set → gr_set → Prop where "x ≡ y" := (gr_eq x y);
    gr_zero : gr_set where "0" := (gr_zero);
    gr_add : gr_set → gr_set → gr_set where "x + y" := (gr_add x y);
    gr_inv : gr_set → gr_set where "- x" := (gr_inv x);
    (* properties *)
    gr_zero_mem : 0 ∈ G;
    gr_add_mem : ∀ x y, x ∈ G → y ∈ G → x + y ∈ G;
    gr_add_0_l : ∀ x, 0 + x ≡ x;
    gr_add_assoc : ∀ x y z, (x + y) + z ≡ x + (y + z);
    gr_inv_mem : ∀ x, x ∈ G → - x ∈ G;
    gr_add_inv_r : ∀ x, x + (- x) ≡ 0;
    gr_add_comm : ∀ x y, x + y ≡ y + x;
    gr_equiv : Equivalence gr_eq;
    gr_mem_compat : ∀ x y, x ≡ y → x ∈ G → y ∈ G;
    gr_add_compat : ∀ x y x' y', x ≡ y → x' ≡ y' → x + x' ≡ y + y';
    gr_inv_compat : ∀ x y, x ≡ y → - x ≡ - y }.

(* coq stuff: implicit and renamed arguments *)

Arguments gr_eq [_].
Arguments gr_zero [_].
Arguments gr_add [_].
Arguments gr_inv [_].
Arguments gr_zero_mem G : rename.
Arguments gr_add_mem G : rename.
Arguments gr_add_0_l G : rename.
Arguments gr_add_assoc G : rename.
Arguments gr_inv_mem G : rename.
Arguments gr_add_inv_r G : rename.
Arguments gr_add_comm G : rename.
Arguments gr_equiv G : rename.
Arguments gr_mem_compat G : rename.
Arguments gr_add_compat G : rename.
Arguments gr_inv_compat G : rename.

(* syntaxes for expressions for groups elements and sets *)

Delimit Scope group_scope with G.

Notation "0" := (gr_zero) : group_scope.
Notation "a = b" := (gr_eq a b) : group_scope.
Notation "a ≠ b" := (¬ gr_eq a b) : group_scope.
Notation "a + b" := (gr_add a b) : group_scope.
Notation "a - b" := (gr_add a (gr_inv b)) : group_scope.
Notation "- a" := (gr_inv a) : group_scope.

Notation "x '∈' S" := (gr_mem S x) (at level 60).
Notation "x '∉' S" := (¬ gr_mem S x) (at level 60).

Open Scope group_scope.

(* Homomorphism between groups *)

Record HomGr (A B : AbGroup) :=
  { Happ : gr_set A → gr_set B;
    Hmem_compat : ∀ x, x ∈ A → Happ x ∈ B;
    Happ_compat : ∀ x y,
      x ∈ A → y ∈ A → (x = y)%G → (Happ x = Happ y)%G;
    Hadditive : ∀ x y,
      x ∈ A → y ∈ A → (Happ (x + y) = Happ x + Happ y)%G }.

(* coq stuff: implicit and renamed arguments *)

Arguments Happ [A] [B].
Arguments Hmem_compat _ _ f : rename.
Arguments Happ_compat _ _ f : rename.
Arguments Hadditive _ _ f : rename.

(* Equality (gr_eq) in groups is an equivalence relation *)

Add Parametric Relation {G} : (gr_set G) (@gr_eq G)
 reflexivity proved by (@Equivalence_Reflexive _ (@gr_eq G) (@gr_equiv G))
 symmetry proved by (@Equivalence_Symmetric _ (@gr_eq G) (@gr_equiv G))
 transitivity proved by (@Equivalence_Transitive _ (@gr_eq G) (@gr_equiv G))
 as gr_eq_rel.

(* Coq "Morphisms": they allow to use "rewrite" in expressions containing
   inversions (-), additions (+) and memberships (∈) *)

Add Parametric Morphism {G} : (@gr_inv G)
  with signature @gr_eq G ==> @gr_eq G
  as gr_inv_morph.
Proof.
intros * Hxy.
now apply gr_inv_compat.
Qed.

Add Parametric Morphism {G} : (@gr_add G)
  with signature @gr_eq G ==> @gr_eq G ==> @gr_eq G
  as gr_add_morph.
Proof.
intros * Hxy x' y' Hxy'.
now apply gr_add_compat.
Qed.

Add Parametric Morphism {G} : (@gr_mem G)
  with signature @gr_eq G ==> iff
  as gr_mem_morph.
Proof.
intros * Hxy.
split; intros H.
-eapply gr_mem_compat; [ apply Hxy | easy ].
-eapply gr_mem_compat; [ symmetry; apply Hxy | easy ].
Qed.

(*
Definition gr_elem A := { a : gr_set A | a ∈ A }.
Definition gr_mem_eq A (x y : gr_elem A) := (proj1_sig x = proj1_sig y)%G.

Theorem gr_mem_refl {A} : Reflexive (gr_mem_eq A).
Proof.
intros (x & Hx).
now unfold gr_mem_eq.
Qed.

Theorem gr_mem_symm {A} : Symmetric (gr_mem_eq A).
Proof.
intros (x & Hx) (y & Hy).
unfold gr_mem_eq; simpl; intros Hxy.
now symmetry.
Qed.

Theorem gr_mem_trans {A} : Transitive (gr_mem_eq A).
Proof.
intros (x & Hx) (y & Hy) (z & Hz).
unfold gr_mem_eq; simpl; intros Hxy Hyz.
now transitivity y.
Qed.

Add Parametric Relation {G} : _ (@gr_mem_eq G)
 reflexivity proved by gr_mem_refl
 symmetry proved by gr_mem_symm
 transitivity proved by gr_mem_trans
 as gr_mem_rel.

Definition M_app A B (f : HomGr A B) (x : gr_elem A) := Happ f (proj1_sig x).

Add Parametric Morphism {G H} : (M_app G H)
  with signature eq ==> gr_mem_eq G ==> @gr_eq H
  as M_app_morph.
Proof.
intros f (x, Hx) (y, Hy) Hxy.
unfold gr_mem_eq in Hxy; simpl in Hxy.
unfold M_app; simpl.
now apply Happ_compat.
Qed.
*)

(* Miscellaneous theorems in groups *)

Theorem gr_add_0_r : ∀ G (x : gr_set G), (x + 0 = x)%G.
Proof.
intros.
rewrite gr_add_comm.
apply gr_add_0_l.
Qed.

Theorem gr_add_inv_l : ∀ G (x : gr_set G), (- x + x = 0)%G.
Proof.
intros.
rewrite gr_add_comm.
apply gr_add_inv_r.
Qed.

Theorem gr_inv_zero : ∀ G, (- 0 = @gr_zero G)%G.
Proof.
intros.
rewrite <- gr_add_0_l.
apply gr_add_inv_r.
Qed.

Theorem gr_sub_0_r : ∀ G (x : gr_set G), (x - 0 = x)%G.
Proof.
intros.
symmetry; rewrite <- gr_add_0_r at 1.
apply gr_add_compat; [ easy | now rewrite gr_inv_zero ].
Qed.

Theorem gr_sub_move_r : ∀ G (x y z : gr_set G),
  (x - y = z)%G ↔ (x = z + y)%G.
Proof.
intros.
split; intros Hxyz.
-now rewrite <- Hxyz, gr_add_assoc, gr_add_inv_l, gr_add_0_r.
-now rewrite Hxyz, gr_add_assoc, gr_add_inv_r, gr_add_0_r.
Qed.

Theorem gr_sub_move_l : ∀ G (x y z : gr_set G),
  (x - y = z)%G ↔ (x = y + z)%G.
Proof.
intros.
split; intros Hxyz.
-now rewrite <- Hxyz, gr_add_comm, gr_add_assoc, gr_add_inv_l, gr_add_0_r.
-now rewrite Hxyz, gr_add_comm, <- gr_add_assoc, gr_add_inv_l, gr_add_0_l.
Qed.

Theorem gr_inv_add_distr : ∀ G (x y : gr_set G), (- (x + y) = - x - y)%G.
Proof.
intros *.
symmetry.
apply gr_sub_move_r.
rewrite <- gr_add_0_l.
apply gr_sub_move_r.
symmetry; rewrite gr_add_assoc.
symmetry.
apply gr_sub_move_r.
rewrite gr_add_0_l.
apply gr_inv_compat, gr_add_comm.
Qed.

Theorem gr_inv_involutive : ∀ G (x : gr_set G), (- - x = x)%G.
Proof.
intros.
transitivity (- - x + (- x + x))%G.
-rewrite <- gr_add_0_r at 1.
 apply gr_add_compat; [ easy | ].
 now rewrite gr_add_inv_l.
-now rewrite <- gr_add_assoc, gr_add_inv_l, gr_add_0_l.
Qed.

Theorem gr_eq_inv_l : ∀ G (x y : gr_set G), (- x = y)%G ↔ (x = - y)%G.
Proof.
intros.
split; intros Hxy.
-rewrite <- Hxy; symmetry; apply gr_inv_involutive.
-rewrite Hxy; apply gr_inv_involutive.
Qed.

(* Theorems on homomorphisms *)

Theorem Hzero : ∀ A B (f : HomGr A B), (Happ f 0 = 0)%G.
Proof.
intros.
assert (H1 : (@gr_zero A + 0 = 0)%G) by apply A.
assert (H2 : (Happ f 0 + Happ f 0 = Happ f 0)%G). {
  rewrite <- Hadditive; [ | apply A | apply A ].
  apply f; [ apply A; apply A | apply A | easy ].
}
assert (H3 : (Happ f 0 + Happ f 0 - Happ f 0 = Happ f 0 - Happ f 0)%G). {
  apply gr_add_compat; [ apply H2 | easy ].
}
assert (H4 : (Happ f 0 + Happ f 0 - Happ f 0 = 0)%G). {
  rewrite H3; apply gr_add_inv_r.
}
rewrite <- H4.
now rewrite gr_add_assoc, gr_add_inv_r, gr_add_0_r.
Qed.

Theorem Hinv : ∀ A B (f : HomGr A B) x,
  x ∈ A → (Happ f (- x) = - Happ f x)%G.
Proof.
intros * Hx.
assert (H1 : (x - x = 0)%G) by apply A.
assert (H2 : (Happ f (x - x) = Happ f 0)%G). {
  apply Happ_compat; [ now apply A, A | apply A | apply H1 ].
}
assert (H3 : (Happ f x + Happ f (- x) = Happ f 0)%G). {
  rewrite <- H2.
  symmetry; apply Hadditive; [ easy | now apply A ].
}
assert (H4 : (Happ f x + Happ f (- x) = 0)%G). {
  rewrite H3; apply Hzero.
}
symmetry; rewrite <- gr_add_0_l.
apply gr_sub_move_l.
now symmetry.
Qed.

(* Images *)

Theorem Im_zero_mem {G H} : ∀ (f : HomGr G H),
  ∃ a : gr_set G, a ∈ G ∧ (Happ f a = 0)%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | apply Hzero ].
Qed.

Theorem Im_add_mem {G H} : ∀ f (x y : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (Happ f a = x)%G)
  → (∃ a : gr_set G, a ∈ G ∧ (Happ f a = y)%G)
  → ∃ a : gr_set G, a ∈ G ∧ (Happ f a = x + y)%G.
Proof.
intros f y y' (x & Hxg & Hx) (x' & Hx'g & Hx').
exists (gr_add x x').
split; [ now apply G | ].
rewrite Hadditive; [ | easy | easy ].
now apply gr_add_compat.
Qed.

Theorem Im_inv_mem {G H} : ∀ (f : HomGr G H) (x : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (Happ f a = x)%G)
  → ∃ a : gr_set G, a ∈ G ∧ (Happ f a = - x)%G.
Proof.
intros f x (y & Hy & Hyx).
exists (gr_inv y).
split; [ now apply gr_inv_mem | ].
rewrite <- Hyx.
now apply Hinv.
Qed.

Theorem Im_mem_compat {G H} : ∀ f (x y : gr_set H),
  (x = y)%G
  → (∃ a, a ∈ G ∧ (Happ f a = x)%G)
  → ∃ a, a ∈ G ∧ (Happ f a = y)%G.
intros * Hxy (z & Hz & Hfz).
exists z.
split; [ easy | now rewrite Hfz ].
Qed.

Definition Im {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := @gr_eq H;
     gr_mem := λ b, ∃ a, a ∈ G ∧ (Happ f a = b)%G;
     gr_add := @gr_add H;
     gr_inv := @gr_inv H;
     gr_zero_mem := Im_zero_mem f;
     gr_add_mem := Im_add_mem f;
     gr_add_0_l := gr_add_0_l H;
     gr_add_assoc := gr_add_assoc H;
     gr_inv_mem := Im_inv_mem f;
     gr_add_inv_r := gr_add_inv_r H;
     gr_add_comm := gr_add_comm H;
     gr_equiv := gr_equiv H;
     gr_mem_compat := Im_mem_compat f;
     gr_add_compat := gr_add_compat H;
     gr_inv_compat := gr_inv_compat H |}.

(* Kernels *)

Theorem Ker_zero_mem {G H} : ∀ (f : HomGr G H), 0%G ∈ G ∧ (Happ f 0 = 0)%G.
Proof.
intros f.
split; [ apply gr_zero_mem | apply Hzero ].
Qed.

Theorem Ker_add_mem {G H} : ∀ (f : HomGr G H) (x y : gr_set G),
  x ∈ G ∧ (Happ f x = 0)%G
  → y ∈ G ∧ (Happ f y = 0)%G → (x + y)%G ∈ G ∧ (Happ f (x + y) = 0)%G.
Proof.
intros f x x' (Hx, Hfx) (Hx', Hfx').
split; [ now apply gr_add_mem | ].
rewrite Hadditive; [ | easy | easy ].
rewrite Hfx, Hfx'.
apply gr_add_0_r.
Qed.

Theorem Ker_inv_mem {G H} : ∀ (f : HomGr G H) (x : gr_set G),
  x ∈ G ∧ (Happ f x = 0)%G → (- x)%G ∈ G ∧ (Happ f (- x) = 0)%G.
Proof.
intros f x (Hx & Hfx).
split; [ now apply gr_inv_mem | ].
rewrite Hinv; [ | easy ].
rewrite Hfx.
apply gr_inv_zero.
Qed.

Theorem Ker_mem_compat {G H} : ∀ (f : HomGr G H) x y,
  (x = y)%G → x ∈ G ∧ (Happ f x = 0)%G → y ∈ G ∧ (Happ f y = 0)%G.
Proof.
intros * Hxy (ax, Hx).
split.
-eapply gr_mem_compat; [ apply Hxy | easy ].
-rewrite <- Hx.
 apply f; [ | easy | easy ].
 now rewrite <- Hxy.
Qed.

Definition Ker {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set G;
     gr_zero := gr_zero;
     gr_eq := @gr_eq G;
     gr_mem := λ a, a ∈ G ∧ (Happ f a = gr_zero)%G;
     gr_add := @gr_add G;
     gr_inv := @gr_inv G;
     gr_zero_mem := Ker_zero_mem f;
     gr_add_mem := Ker_add_mem f;
     gr_add_0_l := gr_add_0_l G;
     gr_add_assoc := gr_add_assoc G;
     gr_inv_mem := Ker_inv_mem f;
     gr_add_inv_r := gr_add_inv_r G;
     gr_add_comm := gr_add_comm G;
     gr_equiv := gr_equiv G;
     gr_mem_compat := Ker_mem_compat f;
     gr_add_compat := gr_add_compat G;
     gr_inv_compat := gr_inv_compat G |}.

(* Exact sequences *)

Inductive sequence {A : AbGroup} :=
  | SeqEnd : sequence
  | Seq : ∀ {B} (f : HomGr A B), @sequence B → sequence.

Notation "A ⊂ B" := (∀ a, a ∈ A → a ∈ B) (at level 60).
Notation "A == B" := (A ⊂ B ∧ B ⊂ A) (at level 60).

Fixpoint exact_sequence {A : AbGroup} (S : sequence) :=
  match S with
  | SeqEnd => True
  | Seq f S' =>
      match S' with
      | SeqEnd => True
      | Seq g S'' => Im f == Ker g ∧ exact_sequence S'
      end
  end.

Delimit Scope seq_scope with S.

Notation "[ ]" := SeqEnd (format "[ ]") : seq_scope.
Notation "[ x ]" := (Seq x SeqEnd) : seq_scope.
Notation "[ x ; y ; .. ; z ]" := (Seq x (Seq y .. (Seq z SeqEnd) ..)) : seq_scope.

Arguments exact_sequence _ S%S.

(* Commuting diagram
        f
    A------>B
    |       |
   g|       |h
    |       |
    v       v
    C------>D
        k
*)

Definition diagram_commutes {A B C D}
     (f : HomGr A B) (g : HomGr A C) (h : HomGr B D) (k : HomGr C D) :=
  ∀ x, (Happ h (Happ f x) = Happ k (Happ g x))%G.

(* The trivial group *)

Inductive Gr0_set := G0 : Gr0_set.

Theorem Gr0_add_0_l : ∀ x, (λ _ _ : Gr0_set, G0) G0 x = x.
Proof.
now intros x; destruct x.
Qed.

Definition Gr0 :=
   {| gr_set := Gr0_set;
      gr_mem _ := True;
      gr_eq := eq;
      gr_zero := G0;
      gr_add _ _ := G0;
      gr_inv x := x;
      gr_zero_mem := I;
      gr_add_mem _ _ _ _ := I;
      gr_add_0_l := Gr0_add_0_l;
      gr_add_assoc _ _ _ := eq_refl G0;
      gr_inv_mem _ H := H;
      gr_add_inv_r _ := eq_refl;
      gr_add_comm _ _ := eq_refl G0;
      gr_equiv := eq_equivalence;
      gr_mem_compat _ _ _ _ := I;
      gr_add_compat _ _ _ _ _ _ := eq_refl;
      gr_inv_compat _ _ H := H |}.

(* We sometimes need these axioms *)

Axiom Function_of_Relation : ∀ {A B} {R : A → B → Prop},
   (∀ x : A, ∃ y : B, R x y) → ∃ f : A → B, ∀ x : A, R x (f x).
Axiom MemDec : ∀ G x, {x ∈ G} + {x ∉ G}.
