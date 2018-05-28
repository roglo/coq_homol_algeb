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
  { H_app : gr_set A → gr_set B;
    H_mem_compat : ∀ x, x ∈ A → H_app x ∈ B;
    H_app_compat : ∀ x y,
      x ∈ A → y ∈ A → (x = y)%G → (H_app x = H_app y)%G;
    H_additive : ∀ x y,
      x ∈ A → y ∈ A → (H_app (x + y) = H_app x + H_app y)%G }.

(* coq stuff: implicit and renamed arguments *)

Arguments H_app [A] [B].
Arguments H_mem_compat _ _ f : rename.
Arguments H_app_compat _ _ f : rename.
Arguments H_additive _ _ f : rename.
