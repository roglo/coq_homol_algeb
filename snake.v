(* Snake lemma *)

Require Import Utf8.
Require Import Classes.RelationClasses.
Require Import Setoid.
Require ClassicalChoice.

Reserved Notation "x '∈' S" (at level 60).
Reserved Notation "x '≡' y" (at level 70).

(* Abelian Groups.

   Notes:

   -sets in groups are represented by predicates; so a value of type
    gr_set is not necessarily in the group set. To be in the group set, it
    must satisfy the predicate gr_mem, which is later syntaxified by the
    usual symbol ∈.

   -moreover group sets are setoids: there is a specific equality (gr_eq)
    which must be compatible with membership (gr_mem_compat), with addition
    (gr_add_compat), and with inverse (gr_inv_compat). This allows to define
    quotient groups by changing this equality, for example in cokernels
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

Notation "x '∈' S" := (gr_mem S x) (at level 60).
Notation "x '∉' S" := (¬ gr_mem S x) (at level 60).
Notation "x '≡' y" := (gr_eq x y) (at level 70).

Delimit Scope group_scope with G.

Notation "0" := (gr_zero) : group_scope.
Notation "a = b" := (gr_eq a b) : group_scope.
Notation "a ≠ b" := (¬ gr_eq a b) : group_scope.
Notation "a + b" := (gr_add a b) : group_scope.
Notation "a - b" := (gr_add a (gr_inv b)) : group_scope.
Notation "- a" := (gr_inv a) : group_scope.

Add Parametric Relation {G} : (gr_set G) (@gr_eq G)
 reflexivity proved by (@Equivalence_Reflexive _ (@gr_eq G) (@gr_equiv G))
 symmetry proved by (@Equivalence_Symmetric _ (@gr_eq G) (@gr_equiv G))
 transitivity proved by (@Equivalence_Transitive _ (@gr_eq G) (@gr_equiv G))
 as gr_eq_rel.

Axiom MemDec : ∀ G x, {x ∈ G} + {x ∉ G}.

Open Scope group_scope.

Record HomGr (A B : AbGroup) :=
  { H_app : gr_set A → gr_set B;
    H_mem_compat : ∀ x, x ∈ A → H_app x ∈ B;
    H_linear : ∀ x y, x ∈ A → y ∈ A → (H_app (x + y) = H_app x + H_app y)%G;
    H_compat : ∀ x y, x ∈ A → y ∈ A → (x = y)%G → (H_app x = H_app y)%G }.

Arguments H_app [A] [B].
Arguments H_mem_compat _ _ f : rename.
Arguments H_linear _ _ f : rename.
Arguments H_compat _ _ f : rename.

Theorem gr_eq_trans : ∀ G (x y z : gr_set G), x ≡ y → y ≡ z → x ≡ z.
Proof.
apply gr_equiv.
Qed.

Theorem gr_add_0_r : ∀ G (x : gr_set G), (x + 0 = x)%G.
Proof.
intros.
etransitivity; [ apply gr_add_comm | ].
apply gr_add_0_l.
Qed.

Theorem gr_add_inv_l : ∀ G (x : gr_set G), (- x + x = 0)%G.
Proof.
intros.
etransitivity; [ apply gr_add_comm | ].
apply gr_add_inv_r.
Qed.

Theorem gr_inv_zero : ∀ G, (- 0 = @gr_zero G)%G.
Proof.
intros.
specialize (@gr_add_inv_r G gr_zero) as H1.
specialize (@gr_add_0_l G (gr_inv gr_zero)) as H3.
etransitivity; [ | apply H1 ].
now symmetry.
Qed.

Theorem gr_sub_0_r : ∀ G (x : gr_set G), (x - 0 = x)%G.
Proof.
intros.
etransitivity; [ | apply gr_add_0_r ].
apply gr_add_compat; [ easy | apply gr_inv_zero ].
Qed.

Theorem gr_sub_move_r : ∀ G (x y z : gr_set G),
  (x - y = z)%G ↔ (x = z + y)%G.
Proof.
intros.
split; intros Hxyz.
-transitivity ((x - y) + y)%G.
 +symmetry.
  etransitivity; [ apply gr_add_assoc | ].
  transitivity (x + 0)%G.
  *apply gr_add_compat; [ reflexivity | apply gr_add_inv_l ].
  *apply gr_add_0_r.
 +apply gr_add_compat; [ easy | reflexivity ].
-transitivity (z + y - y)%G.
 +apply gr_add_compat; [ easy | reflexivity ].
 +etransitivity; [ apply gr_add_assoc | ].
  transitivity (z + 0)%G.
  *apply gr_add_compat; [ reflexivity | apply gr_add_inv_r ].
  *apply gr_add_0_r.
Qed.

Theorem gr_sub_move_l : ∀ G (x y z : gr_set G),
  (x - y = z)%G ↔ (x = y + z)%G.
Proof.
intros.
split; intros Hxyz.
-symmetry.
 etransitivity; [ apply gr_add_comm | ].
 now symmetry; apply gr_sub_move_r.
-apply gr_sub_move_r.
 etransitivity; [ apply Hxyz | ].
 apply gr_add_comm.
Qed.

Theorem gr_inv_add_distr : ∀ G (x y : gr_set G), (- (x + y) = - x - y)%G.
Proof.
intros *.
symmetry.
apply gr_sub_move_r.
etransitivity.
-symmetry; apply gr_add_0_l.
-apply gr_sub_move_r.
 symmetry.
 etransitivity; [ apply gr_add_assoc | ].
 transitivity (- (x + y) + (x + y))%G.
 +apply gr_add_compat; [ reflexivity | apply gr_add_comm ].
 +apply gr_add_inv_l.
Qed.

Theorem gr_inv_inv : ∀ G (x : gr_set G), (- - x = x)%G.
Proof.
intros.
transitivity (- - x + (- x + x))%G.
-symmetry.
 transitivity (- - x + 0)%G.
 +apply gr_add_compat; [ reflexivity | apply gr_add_inv_l ].
 +apply gr_add_0_r.
-etransitivity; [ symmetry; apply gr_add_assoc | ].
 etransitivity; [ | apply gr_add_0_l ].
 apply gr_add_compat; [ apply gr_add_inv_l | reflexivity ].
Qed.

Theorem H_zero : ∀ A B (f : HomGr A B), (H_app f 0 = 0)%G.
Proof.
intros.
assert (H1 : (@gr_zero A + 0 = 0)%G) by apply A.
assert (H2 : (H_app f 0 + H_app f 0 = H_app f 0)%G). {
  etransitivity; [ symmetry; apply f; apply A | ].
  apply f; [ apply A; apply A | apply A | apply A ].
}
assert (H3 : (H_app f 0 + H_app f 0 - H_app f 0 = H_app f 0 - H_app f 0)%G). {
  apply gr_add_compat; [ apply H2 | reflexivity ].
}
assert (H4 : (H_app f 0 + H_app f 0 - H_app f 0 = 0)%G). {
  etransitivity; [ apply H3 | apply B ].
}
etransitivity; [ | apply H4 ].
symmetry.
etransitivity; [ apply gr_add_assoc | ].
etransitivity; [ | apply gr_add_0_r ].
apply gr_add_compat; [ reflexivity | apply B ].
Qed.

Theorem H_inv : ∀ A B (f : HomGr A B) x,
  x ∈ A → (H_app f (- x) = - H_app f x)%G.
Proof.
intros * Hx.
assert (H1 : (x - x = 0)%G) by apply A.
assert (H2 : (H_app f (x - x) = H_app f 0)%G). {
  apply H_compat; [ now apply A, A | apply A | apply H1 ].
}
assert (H3 : (H_app f x + H_app f (- x) = H_app f 0)%G). {
  etransitivity; [ | apply H2 ].
  symmetry; apply H_linear; [ easy | now apply A ].
}
assert (H4 : (H_app f x + H_app f (- x) = 0)%G). {
  etransitivity; [ apply H3 | apply H_zero ].
}
transitivity (0 - H_app f x)%G.
-now symmetry; apply gr_sub_move_l; symmetry.
-apply gr_add_0_l.
Qed.

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

Definition is_initial (G : AbGroup) :=
  ∀ H (f g : HomGr G H) (x : gr_set G), H_app f x ≡ H_app g x.
Definition is_final (G : AbGroup) :=
  ∀ H (f g : HomGr H G) (x : gr_set H), H_app f x ≡ H_app g x.
Definition is_null (G : AbGroup) := is_initial G ∧ is_final G.

Theorem is_null_Gr0 : is_null Gr0.
Proof.
split; intros H f g x.
-destruct x.
 apply gr_eq_trans with (y := gr_zero); [ apply H_zero | ].
 symmetry; apply H_zero.
-now destruct (H_app f x), (H_app g x).
Qed.

Theorem Im_zero_mem {G H} : ∀ (f : HomGr G H),
  ∃ a : gr_set G, a ∈ G ∧ (H_app f a = 0)%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | apply H_zero ].
Qed.

Theorem Im_add_mem {G H} : ∀ f (x y : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (H_app f a = x)%G)
  → (∃ a : gr_set G, a ∈ G ∧ (H_app f a = y)%G)
  → ∃ a : gr_set G, a ∈ G ∧ (H_app f a = x + y)%G.
Proof.
intros f y y' (x & Hxg & Hx) (x' & Hx'g & Hx').
exists (gr_add x x').
split; [ now apply G | ].
etransitivity; [ now apply H_linear | ].
transitivity (gr_add y y').
+now apply gr_add_compat.
+reflexivity.
Qed.

Theorem Im_inv_mem {G H} : ∀ (f : HomGr G H) (x : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (H_app f a = x)%G)
  → ∃ a : gr_set G, a ∈ G ∧ (H_app f a = - x)%G.
Proof.
intros f x (y & Hy & Hyx).
exists (gr_inv y).
split; [ now apply gr_inv_mem | ].
transitivity (gr_inv (H_app f y)).
+now apply H_inv.
+now apply gr_inv_compat.
Qed.

Theorem Im_equiv {G} : Equivalence (@gr_eq G).
Proof.
apply gr_equiv.
Show Proof.
Qed.

Theorem Im_mem_compat {G H} : ∀ f (x y : gr_set H),
  (x = y)%G
  → (∃ a, a ∈ G ∧ (H_app f a = x)%G)
  → ∃ a, a ∈ G ∧ (H_app f a = y)%G.
intros * Hxy (z, Hz).
exists z.
split; [ easy | ].
etransitivity; [ apply Hz | easy ].
Qed.

Definition Im {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := @gr_eq H;
     gr_mem := λ b, ∃ a, a ∈ G ∧ H_app f a ≡ b;
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

Theorem Ker_zero_mem {G H} : ∀ (f : HomGr G H), 0%G ∈ G ∧ (H_app f 0 = 0)%G.
Proof.
intros f.
split; [ apply gr_zero_mem | apply H_zero ].
Qed.

Theorem Ker_add_mem {G H} : ∀ (f : HomGr G H) (x y : gr_set G),
  x ∈ G ∧ (H_app f x = 0)%G
  → y ∈ G ∧ (H_app f y = 0)%G → (x + y)%G ∈ G ∧ (H_app f (x + y) = 0)%G.
Proof.
intros f x x' (Hx, Hfx) (Hx', Hfx').
split; [ now apply gr_add_mem | ].
etransitivity; [ now apply H_linear | ].
etransitivity; [ | apply gr_add_0_l ].
now apply gr_add_compat.
Qed.

Theorem Ker_inv_mem {G H} : ∀ (f : HomGr G H) (x : gr_set G),
  x ∈ G ∧ (H_app f x = 0)%G → (- x)%G ∈ G ∧ (H_app f (- x) = 0)%G.
Proof.
intros f x (Hx & Hfx).
split.
+now apply gr_inv_mem.
+etransitivity; [ now apply H_inv | ].
 etransitivity; [ apply gr_inv_compat, Hfx | ].
 apply gr_inv_zero.
Qed.

Theorem Ker_mem_compat {G H} : ∀ (f : HomGr G H) x y,
  (x = y)%G → x ∈ G ∧ (H_app f x = 0)%G → y ∈ G ∧ (H_app f y = 0)%G.
Proof.
intros * Hxy (ax, Hx).
split.
-eapply gr_mem_compat; [ apply Hxy | easy ].
-etransitivity; [ | apply Hx ].
 symmetry.
 apply H_compat; [ easy | | easy ].
 eapply gr_mem_compat; [ apply Hxy | easy ].
Qed.

Definition Ker {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set G;
     gr_zero := gr_zero;
     gr_eq := @gr_eq G;
     gr_mem := λ a, a ∈ G ∧ H_app f a ≡ gr_zero;
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

Definition gr_sub {G} (x y : gr_set G) := gr_add x (gr_inv y).

(* x ∈ Coker f ↔ x ∈ H/Im f
   quotient group is H with setoid, i.e. set with its own equality *)

Definition Coker_eq {G H} (f : HomGr G H) x y := (x - y)%G ∈ Im f.

Theorem Coker_add_0_l {G H} : ∀ (f : HomGr G H) x, Coker_eq f (0 + x)%G x.
Proof.
intros.
unfold Coker_eq.
exists 0%G.
split; [ apply gr_zero_mem | ].
etransitivity; [ apply H_zero | ].
symmetry.
simpl in x; simpl.
etransitivity; [ apply gr_add_assoc | ].
etransitivity; [ apply gr_add_0_l | ].
apply gr_add_inv_r.
Qed.

Theorem Coker_add_assoc {G H} : ∀ (f : HomGr G H) x y z,
  Coker_eq f (x + y + z)%G (x + (y + z))%G.
Proof.
intros.
unfold Coker_eq.
exists 0%G.
split; [ apply gr_zero_mem | ].
etransitivity; [ apply H_zero | ].
symmetry.
simpl in x, y, z; simpl.
apply gr_sub_move_r; symmetry.
etransitivity; [ apply gr_add_0_l | ].
symmetry; apply gr_add_assoc.
Qed.

Theorem Coker_add_inv_r {G H} : ∀ (f : HomGr G H) x, Coker_eq f (x - x)%G 0%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | ].
etransitivity; [ apply H_zero | ].
symmetry.
simpl.
apply gr_eq_trans with (y := (0 - 0)%G).
-apply gr_add_compat; [ apply gr_add_inv_r | reflexivity ].
-apply gr_add_inv_r.
Qed.

Theorem Coker_add_comm {G H} : ∀ (f : HomGr G H) x y,
  Coker_eq f (x + y)%G (y + x)%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | ].
etransitivity; [ apply H_zero | ].
symmetry.
simpl.
apply gr_sub_move_r.
etransitivity; [ apply gr_add_comm | ].
symmetry.
etransitivity; [ apply gr_add_0_l | reflexivity ].
Qed.

Theorem Coker_eq_refl {G H} (f : HomGr G H) : Reflexive (Coker_eq f).
Proof.
intros x.
exists 0%G.
split; [ apply gr_zero_mem | ].
etransitivity; [ apply H_zero | ].
simpl.
symmetry; apply gr_add_inv_r.
Qed.

Theorem Coker_eq_symm {G H} (f : HomGr G H) : Symmetric (Coker_eq f).
Proof.
intros x y Hxy.
destruct Hxy as (z & Hz).
exists (- z)%G.
split; [ now apply gr_inv_mem | ].
etransitivity; [ now apply H_inv | ].
transitivity ((- (x - y))%G).
+now simpl; apply gr_inv_compat.
+simpl; etransitivity; [ apply gr_inv_add_distr | ].
 etransitivity; [ apply gr_add_comm | ].
 apply gr_add_compat; [ | reflexivity ].
 apply gr_inv_inv.
Qed.

Theorem Coker_eq_trans {G H} (f : HomGr G H) : Transitive (Coker_eq f).
Proof.
intros x y z Hxy Hyz.
simpl in Hxy, Hyz.
destruct Hxy as (t, Ht).
destruct Hyz as (u, Hu).
exists (t + u)%G.
split; [ now apply gr_add_mem | ].
etransitivity; [ now apply H_linear | ].
transitivity ((x - y + (y - z))%G).
+now simpl; apply gr_add_compat.
+simpl; etransitivity; [ apply gr_add_assoc | ].
 apply gr_add_compat; [ reflexivity | ].
 etransitivity; [ symmetry; apply gr_add_assoc | ].
 transitivity ((0 - z)%G).
 *simpl; apply gr_add_compat; [ apply gr_add_inv_l | reflexivity ].
 *simpl; apply gr_add_0_l.
Qed.

Theorem Coker_equiv {G H} : ∀ (f : HomGr G H), Equivalence (Coker_eq f).
Proof.
intros.
unfold Coker_eq; split.
-apply Coker_eq_refl.
-apply Coker_eq_symm.
-apply Coker_eq_trans.
Qed.

Add Parametric Relation {G H} {f : HomGr G H} : (gr_set (Im f)) (Coker_eq f)
 reflexivity proved by (Coker_eq_refl f)
 symmetry proved by (Coker_eq_symm f)
 transitivity proved by (Coker_eq_trans f)
 as gr_cokereq_rel.

Theorem Coker_mem_compat {G H} : ∀ (f : HomGr G H) x y,
  Coker_eq f x y → x ∈ H → y ∈ H.
Proof.
intros * Heq Hx.
destruct Heq as (z, Hz).
apply gr_mem_compat with (x := (x - H_app f z)%G).
-transitivity ((x - (x - y))%G); simpl.
 +apply gr_add_compat; [ reflexivity | ].
  now apply gr_inv_compat.
 +apply gr_sub_move_r; symmetry.
  etransitivity; [ apply gr_add_comm | ].
  etransitivity; [ apply gr_add_assoc | ].
  transitivity ((x + 0)%G); simpl.
  *apply gr_add_compat; [ reflexivity | apply gr_add_inv_l ].
  *apply gr_add_0_r.
-simpl; apply gr_add_mem; [ easy | ].
 apply gr_inv_mem.
 now apply f.
Qed.

Theorem Coker_add_compat {G H} : ∀ (f : HomGr G H) x y x' y',
  Coker_eq f x y → Coker_eq f x' y' → Coker_eq f (x + x')%G (y + y')%G.
Proof.
intros f x y x' y' (z & Hz & Hfz) (z' & Hz' & Hfz').
exists (z + z')%G.
split.
-now apply gr_add_mem.
-etransitivity; [ now apply f | ].
 transitivity (((x - y) + (x' - y'))%G); simpl.
 +now apply gr_add_compat.
 +etransitivity; [ apply gr_add_assoc | symmetry ].
  etransitivity; [ apply gr_add_assoc | symmetry ].
  apply gr_add_compat; [ reflexivity | ].
  etransitivity; [ apply gr_add_comm | ].
  etransitivity; [ apply gr_add_assoc | ].
  apply gr_add_compat; [ reflexivity | ].
  etransitivity; [ apply gr_add_comm | ].
  symmetry; apply gr_inv_add_distr.
Qed.

Theorem Coker_inv_compat {G H} :∀ (f : HomGr G H) x y,
  Coker_eq f x y → Coker_eq f (- x)%G (- y)%G.
Proof.
intros * (z & Hz & Hfz).
unfold Coker_eq; simpl.
exists (- z)%G.
split; [ now apply gr_inv_mem | ].
etransitivity; [ now apply H_inv | ].
transitivity ((- (x - y))%G); simpl.
-now apply gr_inv_compat.
-apply gr_inv_add_distr.
Qed.

Definition Coker {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := Coker_eq f;
     gr_mem := gr_mem H;
     gr_add := @gr_add H;
     gr_inv := @gr_inv H;
     gr_zero_mem := @gr_zero_mem H;
     gr_add_mem := @gr_add_mem H;
     gr_add_0_l := Coker_add_0_l f;
     gr_add_assoc := Coker_add_assoc f;
     gr_inv_mem := gr_inv_mem H;
     gr_add_inv_r := Coker_add_inv_r f;
     gr_add_comm := Coker_add_comm f;
     gr_equiv := Coker_equiv f;
     gr_mem_compat := Coker_mem_compat f;
     gr_add_compat := Coker_add_compat f;
     gr_inv_compat := Coker_inv_compat f |}.

Inductive sequence {A : AbGroup} :=
  | Seq1 : sequence
  | Seq2 : ∀ {B} (f : HomGr A B), @sequence B → sequence.

Fixpoint exact_sequence {A : AbGroup} (S : sequence) :=
  match S with
  | Seq1 => True
  | Seq2 f S' =>
      match S' with
      | Seq1 => True
      | Seq2 g S'' => (∀ a, a ∈ Im f ↔ a ∈ Ker g) ∧ exact_sequence S'
      end
  end.

(*      f
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
  ∀ x, H_app h (H_app f x) ≡ H_app k (H_app g x).

Theorem KK_mem_compat {A B A' B'} : ∀ (a : HomGr A A') (b : HomGr B B') f f',
  diagram_commutes f a b f'
  → ∀ x : gr_set (Ker a), x ∈ Ker a → H_app f x ∈ Ker b.
intros * Hc * Hx.
split; [ now apply f; simpl in Hx | ].
etransitivity; [ apply Hc | ].
transitivity (H_app f' 0%G).
-apply f'; [ apply a, Hx | apply A' | apply Hx ].
-apply H_zero.
Qed.

Theorem KK_lin {A B A'} : ∀ (f : HomGr A B) (a : HomGr A A'),
  ∀ x y : gr_set (Ker a),
  x ∈ Ker a → y ∈ Ker a → (H_app f (x + y) = H_app f x + H_app f y)%G.
Proof.
intros * Hx Hx'; simpl in Hx, Hx'.
now apply f.
Qed.

Theorem KK_compat {A B A'} : ∀ (f : HomGr A B) (a : HomGr A A'),
  ∀ x y : gr_set (Ker a),
  x ∈ Ker a → y ∈ Ker a → (x = y)%G → (H_app f x = H_app f y)%G.
Proof.
intros * Hx Hy Hxy.
simpl in Hx, Hy.
now apply f.
Qed.

Definition HomGr_Ker_Ker {A B A' B'}
    (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B')
    (Hc : diagram_commutes f a b f') :=
  {| H_app (x : gr_set (Ker a)) := H_app f x : gr_set (Ker b);
     H_mem_compat := KK_mem_compat a b f f' Hc;
     H_linear := KK_lin f a;
     H_compat := KK_compat f a |}.

Theorem CC_mem_compat {A B A' B'} :
  ∀ (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  ∀ x : gr_set (Coker a), x ∈ Coker a → H_app f' x ∈ Coker b.
Proof.
intros * Hx.
now apply f'.
Qed.

Theorem CC_lin {A B A' B'} :
  ∀ (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  ∀ x y : gr_set (Coker a), x ∈ Coker a → y ∈ Coker a
  → @gr_eq (Coker b) (H_app f' (x + y))%G (H_app f' x + H_app f' y)%G.
Proof.
intros * Hx Hy; simpl in Hx, Hy.
exists 0%G.
split; [ apply B | ].
etransitivity; [ apply H_zero | apply B' ].
simpl; apply gr_sub_move_r.
apply B'.
etransitivity; [ apply gr_add_0_l | ].
now apply B', f'.
Qed.

Theorem CC_compat {A B A' B'} :
  ∀ (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  diagram_commutes f a b f'
  → ∀ x y : gr_set (Coker a),
  x ∈ Coker a → y ∈ Coker a → (x = y)%G
  → @gr_eq (Coker b) (H_app f' x) (H_app f' y)%G.
Proof.
intros * Hc * Hx Hy Hxy.
simpl in Hx, Hy, x, y, Hxy; simpl.
destruct Hxy as (z & Hz & Haz).
simpl; unfold Coker_eq; simpl.
exists (H_app f z).
split; [ now apply f | ].
etransitivity; [ apply Hc | ].
transitivity (H_app f' (x - y)%G).
-apply H_compat; [ now apply a | | easy ].
 apply A'; [ easy | now apply A' ].
-etransitivity.
 +apply f'; [ easy | now apply A' ].
 +apply gr_add_compat; [ reflexivity | now apply H_inv ].
Qed.

Definition HomGr_Coker_Coker {A B A' B'}
    (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B')
    (Hc : diagram_commutes f a b f') :=
  {| H_app (x : gr_set (Coker a)) := H_app f' x : gr_set (Coker b);
     H_mem_compat := CC_mem_compat f' a b;
     H_linear := CC_lin f' a b;
     H_compat := CC_compat f f' a b Hc |}.

Theorem exists_ker_C_to_B : ∀ B C C' g (c : HomGr C C') (cz : HomGr C Gr0),
  (∀ a : gr_set (Im g), a ∈ Im g ↔ a ∈ Ker cz)
  → ∀ x : gr_set (Ker c), ∃ y, x ∈ C → y ∈ B ∧ H_app g y ≡ x.
Proof.
intros * sg x.
destruct (MemDec C x) as [H2| H2]; [ | now exists 0%G ].
enough (H : x ∈ Im g). {
  simpl in H.
  destruct H as (y & Hy & Hyx).
  now exists y.
}
apply sg.
split; [ easy | ].
simpl in x; simpl.
destruct cz as (appcz, czin, czlin, czcomp).
simpl.
now destruct (appcz x).
Qed.

Lemma snake :
  ∀ (A B C A' B' C' : AbGroup)
     (f : HomGr A B) (g : HomGr B C)
     (f' : HomGr A' B') (g' : HomGr B' C')
     (a : HomGr A A') (b : HomGr B B') (c : HomGr C C')
     (cz : HomGr C Gr0) (za' : HomGr Gr0 A'),
  diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → exact_sequence (Seq2 f (Seq2 g (Seq2 cz Seq1)))
  → exact_sequence (Seq2 za' (Seq2 f' (Seq2 g' Seq1)))
  → ∃ (fk : HomGr (Ker a) (Ker b)) (gk : HomGr (Ker b) (Ker c))
        (fk' : HomGr (Coker a) (Coker b)) (gk' : HomGr (Coker b) (Coker c)),
     ∃ (d : HomGr (Ker c) (Coker a)),
        exact_sequence (Seq2 fk (Seq2 gk (Seq2 d (Seq2 fk' (Seq2 gk' Seq1))))).
Proof.
intros *.
intros Hcff' Hcgg' s s'.
exists (HomGr_Ker_Ker f f' a b Hcff').
exists (HomGr_Ker_Ker g g' b c Hcgg').
exists (HomGr_Coker_Coker f f' a b Hcff').
exists (HomGr_Coker_Coker g g' b c Hcgg').
destruct s as (sf & sg & _).
destruct s' as (sf' & sg' & _).
specialize (exists_ker_C_to_B B C C' g c cz sg) as H1.
specialize (ClassicalChoice.choice _ H1) as (g₁, Hg₁).
assert
  (Hf'inj :
  ∀ x y, x ∈ A' → y ∈ A' → (H_app f' x = H_app f' y)%G → (x = y)%G). {
  intros * Hx Hy Hxy.
  (* it is because Im(cza')={0}=Ker(f') *)
  assert (H2 : (H_app f' x - H_app f' y = 0)%G). {
    apply gr_sub_move_r.
    etransitivity; [ apply Hxy | ].
    symmetry; apply gr_add_0_l.
  }
  assert (H3 : (H_app f' (x - y) = 0)%G). {
    etransitivity; [ | apply H2 ].
    etransitivity.
    -apply H_linear; [ easy | now apply A' ].
    -apply gr_add_compat; [ reflexivity | now apply H_inv ].
  }
  assert (H4 : (x - y)%G ∈ Ker f'). {
    split; [ | apply H3 ].
    apply A'; [ easy | now apply A' ].
  }
  apply sf' in H4.
  simpl in H4.
  destruct H4 as (z & _ & H4).
  destruct z.
  assert (H5 : (x - y = 0)%G). {
    etransitivity; [ symmetry; apply H4 | ].
    apply H_zero.
  }
  apply gr_sub_move_r in H5.
  etransitivity; [ apply H5 | ].
  apply gr_add_0_l.
}
assert (Hcf'inj : ∀ x y, x ∈ Coker a → y ∈ Coker a → (H_app f' x = H_app f' y)%G → (x = y)%G). {
  intros * Hx Hy Hxy.
  simpl; unfold Coker_eq; simpl.
  exists 0; split; [ apply A | ].
  apply Hf'inj; [ apply a, A | | ].
  -apply A'; [ easy | now apply A' ].
  -transitivity (H_app f' 0).
   +apply f'; [ apply a, A | apply A' | apply H_zero ].
   +etransitivity; [ apply H_zero | ].
    symmetry.
    etransitivity.
    *apply H_linear; [ easy | now apply A' ].
    *etransitivity.
    --apply gr_add_compat; [ reflexivity | ].
      now apply H_inv.
    --apply gr_sub_move_r.
      etransitivity; [ apply Hxy | ].
      symmetry; apply gr_add_0_l.
}
assert (H7 : ∀ x, x ∈ C → g₁ x ∈ B). {
  intros z Hz; specialize (Hg₁ z) as H; now destruct H.
}
assert (H5 : ∀ x, x ∈ Ker c → (H_app g' (H_app b (g₁ x)) = 0)%G). {
  intros z (Hz, Hcz).
  specialize (Hg₁ z Hz) as H5.
  etransitivity.
  -symmetry; apply Hcgg'.
  -transitivity (H_app c z); [ | easy ].
   apply H_compat; [ now apply g | easy | easy ].
}
assert
  (H2 :
   ∀ y', ∃ z',
   (∃ x, x ∈ Ker c ∧ (y' = H_app b (g₁ x))%G)
   → z' ∈ Coker a ∧ (H_app f' z' = y')%G). {
  intros y'.
  destruct (MemDec (Im b) y') as [Hy'| Hy'].
  -destruct (MemDec (Im f') y') as [(z' & Hz' & Hfz')| Hfy'].
   +exists z'; now intros (x' & Hx' & Hyx').
   +exists 0%G; intros (x' & Hx' & Hyx').
    exfalso; apply Hfy', sg'; simpl.
    split.
    *destruct Hy' as (y & Hy & Hby).
     eapply B'; [ apply Hby | now apply b ].
    *transitivity (H_app g' (H_app b (g₁ x'))).
    --apply g'; [ | | easy ].
     ++destruct Hy' as (y & Hy & Hby).
       eapply B'; [ apply Hby | now apply b ].
     ++apply b, H7, Hx'.
    --etransitivity; [ symmetry; apply Hcgg' | ].
      destruct Hx' as (Hx', Hcx').
      specialize (Hg₁ x' Hx') as H2.
      destruct H2 as (Hgx', Hggx').
      transitivity (H_app c x'); [ | easy ].
      apply c; [ now apply g, H7| easy | easy ].
  -exists 0%G; intros (x' & Hx' & Hyx').
   exfalso; apply Hy'.
   exists (g₁ x').
   split; [ apply H7; now simpl in Hx' | ].
   now symmetry.
}
specialize (ClassicalChoice.choice _ H2) as (f'₁, Hf'₁).
move f'₁ before g₁.
clear H1 H2.
set (d := λ x, f'₁ (H_app b (g₁ x))).
assert (Hmemc : ∀ x, x ∈ Ker c → d x ∈ Coker a). {
  intros x Hx.
  apply Hf'₁.
  exists x; split; [ easy | reflexivity ].
}
assert
  (Hlin : ∀ x1 x2, x1 ∈ Ker c → x2 ∈ Ker c → (d (x1 + x2) = d x1 + d x2)%G). {
  intros x1 x2 Hx1 Hx2.
  set (x3 := (x1 + x2)%G).
  set (y1 := g₁ x1).
  set (y2 := g₁ x2).
  set (y3 := g₁ x3).
  set (z1 := d x1).
  set (z2 := d x2).
  set (z3 := d x3).
  assert (H1 : (H_app g y1 = x1)%G) by now apply Hg₁; simpl in Hx1.
  assert (H2 : (H_app g y2 = x2)%G) by now apply Hg₁; simpl in Hx2.
  assert (H3 : (H_app g (y1 + y2)%G = x3)%G). {
    etransitivity.
    -apply g.
     +now apply H7; simpl in Hx1.
     +now apply H7; simpl in Hx2.
    -etransitivity.
     +apply gr_add_compat; [ apply H1 | apply H2 ].
     +reflexivity.
  }
  assert (Hy1 : y1 ∈ B) by apply H7, Hx1.
  assert (Hy2 : y2 ∈ B) by apply H7, Hx2.
  assert (Hy3 : y3 ∈ B) by (apply H7, C; [ apply Hx1 | apply Hx2 ]).
  assert (H4 : (y1 + y2 - y3)%G ∈ Ker g). {
    split.
    -now apply B; apply B.
    -etransitivity; [ now apply g; apply B | ].
     symmetry; apply gr_sub_move_r.
     etransitivity; [ apply gr_add_0_l | ].
     etransitivity; [ now apply gr_inv_compat, H_inv | ].
     etransitivity; [ apply gr_inv_inv | ].
     etransitivity.
     +apply Hg₁, C; [ apply Hx1 | apply Hx2 ].
     +symmetry; etransitivity; [ now apply g | ].
      etransitivity.
      *apply gr_add_compat; [ apply H1 | apply H2 ].
      *reflexivity.
  }
  assert (Hfx1 : (H_app f' z1 = H_app b y1)%G). {
    apply Hf'₁; exists x1.
    split; [ easy | reflexivity ].
  }
  assert (Hfx2 : (H_app f' z2 = H_app b y2)%G). {
    apply Hf'₁; exists x2.
    split; [ easy | reflexivity ].
  }
  assert (Hfx3 : (H_app f' z3 = H_app b y3)%G). {
    unfold z3, y3.
    apply Hf'₁.
    exists x3.
    split; [ | reflexivity ].
    unfold x3.
    now apply (Ker c).
  }
  assert
    (Hfzzz :
       (H_app f' (z1 + z2 - z3) = H_app b y1 + H_app b y2 - H_app b y3)%G). {
    assert (Hz1A' : z1 ∈ A' ∧ z2 ∈ A' ∧ z3 ∈ A'). {
      assert (H : z1 ∈ A' ∧ z2 ∈ A'). {
        split.
        -apply Hf'₁.
         exists x1; split; [ easy | reflexivity ].
        -apply Hf'₁.
         exists x2; split; [ easy | reflexivity ].
      }
      split; [ easy | ].
      split; [ easy | ].
      unfold z3.
      apply Hf'₁.
      exists x3; split; [ | reflexivity ].
      unfold x3.
      now apply (Ker c).
    }
    etransitivity; simpl.
    -now apply H_linear; apply A'.
    -apply gr_add_compat.
     +etransitivity; [ now apply H_linear | ].
      now apply gr_add_compat.
     +etransitivity; [ now apply H_inv | ].
      now apply gr_inv_compat.
  }
  apply sf in H4.
  destruct H4 as (z & Hz & Hzf).
  assert (Hfz : (H_app f' (z1 + z2 - z3) = H_app f' (H_app a z))%G). {
    etransitivity; [ apply Hfzzz | ].
    etransitivity.
    -apply gr_add_compat; [ now symmetry; apply b | ].
     +now symmetry; apply H_inv.
    -etransitivity.
     +now symmetry; apply H_linear; apply B.
     +etransitivity.
      *apply H_compat; [ | | symmetry; apply Hzf ].
      --now apply B; apply B.
      --now apply f.
      *apply Hcff'.
  }
  apply Hf'inj in Hfz.
  -simpl; unfold Coker_eq; simpl.
   exists (- z).
   split; [ now apply A | ].
   etransitivity; [ now apply H_inv | ].
   etransitivity; [ apply gr_inv_compat; symmetry; apply Hfz | ].
   symmetry.
   etransitivity; [ apply gr_add_comm | ].
   etransitivity.
   +apply gr_add_compat; [ apply gr_inv_add_distr | reflexivity ].
   +symmetry.
    etransitivity.
    *simpl; apply gr_inv_add_distr.
    *apply gr_add_compat; [ apply gr_inv_add_distr | ].
     apply gr_inv_inv.
  -apply A'.
   +apply A'.
    *apply Hf'₁; exists x1.
     split; [ easy | reflexivity ].
    *apply Hf'₁; exists x2.
     split; [ easy | reflexivity ].
   +apply A'.
    apply Hf'₁; exists x3.
    split; [ | reflexivity ].
    unfold x3.
    now apply (Ker c).
  -now apply a.
}
assert
  (Hcomp :
     ∀ x1 x2, x1 ∈ Ker c → x2 ∈ Ker c → (x1 = x2)%G → (d x1 = d x2)%G). {
  intros * Hx1 Hx2 Hxx.
  assert (Hgy1 : (H_app g (g₁ x1) = x1)%G) by apply Hg₁, Hx1.
  assert (Hgy2 : (H_app g (g₁ x2) = x2)%G) by apply Hg₁, Hx2.
  assert (Hgb1 : (H_app g' (H_app b (g₁ x1)) = 0)%G). {
    etransitivity; [ symmetry; apply Hcgg' | ].
    etransitivity; [ | apply Hx1 ].
    apply c; [ apply g, Hg₁, Hx1 | apply Hx1 | apply Hgy1 ].
  }
  assert (Hgb2 : (H_app g' (H_app b (g₁ x2)) = 0)%G). {
    etransitivity; [ symmetry; apply Hcgg' | ].
    etransitivity; [ | apply Hx2 ].
    apply c; [ apply g, Hg₁, Hx2 | apply Hx2 | apply Hgy2 ].
  }
  assert (H1 : H_app b (g₁ x1) ∈ Im f'). {
    apply sg'; split; [ apply b, H7, Hx1 | easy ].
  }
  assert (H2 : H_app b (g₁ x2) ∈ Im f'). {
    apply sg'; split; [ apply b, H7, Hx2 | easy ].
  }
  destruct H1 as (z'1 & Hz'1 & Hfz'1).
  destruct H2 as (z'2 & Hz'2 & Hfz'2).
  move z'2 before z'1; move Hz'2 before Hz'1.
  assert (H3 : (H_app f' (z'1 - z'2) = H_app b (g₁ x1 - g₁ x2))%G). {
    etransitivity.
    -apply f'; [ easy | now apply A' ].
    -symmetry.
     etransitivity.
     +apply b; [ apply H7, Hx1 | apply B, H7, Hx2 ].
     +symmetry; apply gr_add_compat; [ easy | ].
      etransitivity; [ now apply H_inv | ].
      symmetry.
      etransitivity; [ apply H_inv, H7, Hx2 | ].
      now apply gr_inv_compat; symmetry.
  }
  assert (H4 : g₁ x1 - g₁ x2 ∈ Im f). {
    apply sf.
    split.
    -apply B; [ apply H7, Hx1 | apply B, H7, Hx2 ].
    -etransitivity.
     +apply g; [ apply H7, Hx1 | apply B, H7, Hx2 ].
     +transitivity (x1 - x2); simpl.
      *apply gr_add_compat; [ easy | ].
       etransitivity; [ apply H_inv, H7, Hx2 | ].
       now apply gr_inv_compat.
      *apply gr_sub_move_r; symmetry.
       etransitivity; [ apply gr_add_0_l | ].
       now symmetry.
  }
  destruct H4 as (z & Hz & Hfz).
  assert (H4 : (z'1 - z'2 = H_app a z)%G). {
    apply Hf'inj; [ | now apply a | ].
    -apply A'; [ easy | now apply A' ].
    -symmetry; etransitivity.
     +symmetry; apply Hcff'.
     +etransitivity.
      *apply H_compat with (y := g₁ x1 - g₁ x2); [ now apply f | | easy ].
       apply B; [ apply H7, Hx1 | apply B, H7, Hx2 ].
      *now symmetry.
  }
  assert (H6 : z'1 - z'2 ∈ Im a). {
    exists z; split; [ easy | now symmetry ].
  }
  assert (Hdx2 : (d x2 = z'2)%G). {
    simpl; unfold Coker_eq; simpl.
    exists 0.
    split; [ apply A | ].
    etransitivity; [ apply H_zero | ].
    symmetry; apply gr_sub_move_r; symmetry.
    etransitivity; [ apply gr_add_0_l | ].
    apply Hf'inj; [ easy | | ].
    -unfold d; apply Hf'₁; exists x2.
     split; [ easy | reflexivity ].
    -etransitivity; [ apply Hfz'2 | ].
     symmetry; apply Hf'₁; exists x2; split; [ easy | reflexivity ].
  }
  assert (Hdx1 : (d x1 = z'1)%G). {
    simpl; unfold Coker_eq; simpl.
    exists 0.
    split; [ apply A | ].
    etransitivity; [ apply H_zero | ].
    symmetry; apply gr_sub_move_r; symmetry.
    etransitivity; [ apply gr_add_0_l | ].
    apply Hf'inj; [ easy | | ].
    -unfold d; apply Hf'₁; exists x1.
     split; [ easy | reflexivity ].
    -etransitivity; [ apply Hfz'1 | ].
     symmetry; apply Hf'₁; exists x1; split; [ easy | reflexivity ].
  }
  assert (Hzz' : @gr_eq (@Coker A A' a) z'1 z'2). {
    destruct H6 as (zz & Hzz & Hazz).
    simpl; unfold Coker_eq; simpl.
    now exists zz; split.
  }
  etransitivity; [ apply Hdx1 | ].
  etransitivity; [ apply Hzz' | ].
  now symmetry.
}
set
  (dm :=
   {| H_app := d; H_mem_compat := Hmemc; H_linear := Hlin;
      H_compat := Hcomp |}).
exists dm.
simpl.
split; [ | split ].
-intros y.
 split.
 +intros (x & (Hx & Hax) & Hxy).
  split; [ split | ].
  *eapply B; [ apply Hxy | now apply f ].
  *transitivity (H_app b (H_app f x)).
  --apply b; [ | now apply f | now symmetry ].
    eapply gr_mem_compat; [ apply Hxy | now apply f ].
  --etransitivity; [ apply Hcff' | ].
    transitivity (H_app f' (@gr_zero A')); [ | apply H_zero ].
    apply f'; [ now apply a | apply A' | easy ].
  *apply sf.
   exists x; easy.
 +intros ((Hy & Hby) & Hgy).
  assert (H : y ∈ Im f) by now apply sf; split.
  destruct H as (x & Hx & Hxy).
  exists x; split; [ | easy ].
  split; [ easy | ].
  specialize (sf' (H_app a x)) as (H1, H2).
  assert (H3 : H_app a x ∈ Ker f'). {
    split; [ now apply a | ].
    specialize (Hcff' x) as H3.
    etransitivity; [ symmetry; apply H3 | ].
    transitivity (H_app b y); [ | easy ].
    apply b; [ | easy | easy ].
    now apply f.
  }
  specialize (H2 H3).
  destruct H2 as (z & _ & Hzz).
  destruct z.
  etransitivity; [ symmetry; apply Hzz | apply H_zero ].
-intros x.
 split.
 +intros (y & (Hy & Hay) & Hyx).
  split; [ split | ].
  *eapply C; [ apply Hyx | now apply g ].
  *specialize (Hcgg' y) as H1.
   transitivity (H_app c (H_app g y)).
  --eapply c; [ | now apply g | now apply C ].
    eapply C; [ apply Hyx | now apply g ].
  --etransitivity; [ apply H1 | ].
    transitivity (H_app g' (@gr_zero B')); [ | apply H_zero ].
    apply g'; [ now apply b | apply B' | easy ].
  *specialize (Hcomp x (H_app g y)) as H1.
   assert (Hgy : H_app g y ∈ Ker c). {
     split; [ now apply g | ].
     etransitivity; [ apply Hcgg' | ].
     etransitivity; [ | apply H_zero ].
     apply g'; [ now apply b | apply B' | easy ].
   }
   assert (Hxk : x ∈ Ker c). {
     assert (Hx : x ∈ C). {
       eapply gr_mem_compat; [ apply Hyx | now apply g ].
     }
     split; [ easy | ].
     etransitivity; [ | apply Hgy ].
     apply c; [ easy | now apply g | now symmetry ].
   }
   symmetry in Hyx.
   specialize (H1 Hxk Hgy Hyx).
   destruct H1 as (z & Hz & Haz).
   unfold Coker_eq; simpl.
...
   split; [ apply A | ].
   etransitivity; [ apply H_zero | ].
   symmetry; etransitivity; simpl; [ apply gr_sub_0_r | ].
   transitivity (d (H_app g y)).
*)
...

  --apply Hcomp.
...
  *transitivity (H_app dm (H_app g y)).
  --eapply dm; [ | | now apply C ].
    split.
   ++eapply C; [ apply Hyx | now apply g ].
   ++transitivity (H_app c (H_app g y)).
    **eapply c; [ | now apply g | now apply C ].
      eapply C; [ apply Hyx | now apply g ].
    **etransitivity; [ apply Hcgg' | ].
      transitivity (H_app g' (@gr_zero B')); [ | apply H_zero ].
      apply g'; [ now apply b | apply B' | easy ].
   ++split; [ now apply g | ].
     etransitivity; [ apply Hcgg' | ].
     transitivity (H_app g' (@gr_zero B')); [ | apply H_zero ].
     apply g'; [ now apply b | apply B' | easy ].
  --unfold dm; simpl.
    unfold Coker_eq; simpl.
    unfold d.
...
   apply sg'; rewrite <- Hxy.
   exists x; easy.
 +intros ((Hy & Hby) & Hgy).
  assert (H : y ∈ Im f) by now apply sf; split.
  destruct H as (x & Hx & Hxy).
  exists x; split; [ | easy ].
  split; [ easy | ].
  rewrite <- Hxy, Hcff' in Hby.
  specialize (sf' (H_app a x)) as (H1, H2).
  assert (H3 : H_app a x ∈ Ker f') by now split; [ apply a | ].
  specialize (H2 H3).
  destruct H2 as (z & _ & Hzz).
  destruct z; rewrite <- Hzz.
  apply za'.
...
