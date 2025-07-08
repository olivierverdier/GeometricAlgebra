From Stdlib Require Import ArithRing Bool QArith List Psatz.
Require Import  Field VectorSpace Kn Clifford Grassmann.

Open Scope Q_scope.

Require Import Field VectorSpace Kn Clifford Grassmann.

Module CGA3D.


Local Definition p := Qparams 5.

Notation " [[ e1: x , e2: y , e3: z , ep: t , em: u , e12: xy , e13: xz , e1p: xt , e1m: xu , e23: yz , e2p: yt , e2m: yu , e3p: zt , e3m: zu , epm: tu , e123: xyz , e12p: xyt , e12m: xyu , e13p: xzt , e13m: xzu , e1pm: xtu , e23p: yzt , e23m: yzu , e2pm: ytu , e3pm: ztu , e123p: xyzt , e123m: xyzu , e12pm: xytu , e13pm: xztu , e23pm: yztu , e123pm: xyztu , K: vv ]]" :=
(
 ((((xyztu, xyzt), (xyzu, xyz)), ((xytu, xyt), (xyu, xy))) , 
  (((xztu, xzt), (xzu, xz)), ((xtu,xt), (xu, x)))),
 ((((yztu, yzt), (yzu, yz)), ((ytu, yt), (yu, y))) , 
  (((ztu, zt), (zu, z)), ((tu,t), (u, vv))))).

Notation "C[ x ]" := (Vgenk p  x).
Notation "x '∨' y" := (Vjoin p  x y) (at level 40, left associativity).
Notation "x + y" := (Vadd p  x y).
Notation "k .* x" := (Vscal p  k x).
Notation "x '∧' y" := (Vmeet p  x y) (at level 40, left associativity).
Notation "'@  x" := (Vdual p x) (at level 100).
Notation "x - y" := (Vadd p x ((-1).*y)).
Notation "x =V y":= (Veq p  x y =true) (at level 50).

SubClass point := Kn (Qparams 3).
SubClass vect := Vect p.

Definition p2v (tuple3 :point) : vect :=
   match tuple3 with
   (a,(b,(c,tt))) => K2G p (a,(b,(c,(0,(0,tt)))))
   end.

   
Coercion p2v : point >-> vect.

Definition l:=(1,(1,(1,(1,(-1, tt))))).
Notation "a *g  b " := (gprod p (dim p) l a b) (at level 9).
Notation "a *s  b " := (prod_scal p (dim p) l a b)  (at level 40).

Definition e_1 := (Vgen p 0).
Eval compute in e_1.
Definition e_2 := (Vgen p 1).
Eval compute in e_2.
Definition e_3 := (Vgen p 2).
Eval compute in e_3.
Definition e_p := (Vgen p 3).
Eval compute in e_p.
Definition e_m := (Vgen p 4).
Eval compute in e_m.
Definition e_0 := (1/2) .*(e_m-e_p).
Compute e_0.

Definition e_inf := e_m+e_p.
Compute e_inf.


Lemma e_0_gsquare : (e_0 *g e_0 =V C[0]).
Proof.
  reflexivity.
Qed.

Lemma e_inf_gsquare : (e_inf *g e_inf =V C[0]).
Proof.
  reflexivity.
Qed.

Lemma outer_e_inf_e_0 : e_inf ∧ e_0 =V e_p ∧ e_m.
Proof.
  reflexivity.
Qed.

Lemma inner_e_inf_null : e_inf *s e_inf == 0.
Proof.
  reflexivity.
Qed.

Lemma inner_e0_null : e_0 *s e_0 == 0.
Proof.
  reflexivity.
Qed.

Lemma inner_e_inf_e_0 : e_inf *s e_0 == -1.
Proof.
  reflexivity.
Qed.

Lemma inner_e_0_e_inf : e_0 *s e_inf == -1.
Proof.
  reflexivity.
Qed.

Definition basevect3D := e_1::e_2::e_3::nil.

Lemma inner_basis_e_inf : forall e, In e basevect3D -> e *s e_inf ==0.
Proof.
  intros e H.
  unfold basevect3D in *.
  simpl In in H.
  intuition; subst; reflexivity.
Qed.

Lemma inner_e_p_e_inf : e_p *s e_inf == 1.
Proof.
  simpl.
 reflexivity.
Qed.

Lemma inner_e_m_e_inf : e_m *s e_inf == -1.
Proof.
  simpl.
 reflexivity.
Qed.

Lemma inner_basis_e_0 : forall e, In e basevect3D -> e *s e_0 ==0.
Proof.
  intros e H.
  unfold basevect3D in *.
  simpl In in H.
  intuition; subst; reflexivity.
Qed.

Lemma inner_e_p_e_0 : e_p *s e_0 == -1#2.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma inner_e_m_e_0 : e_m *s e_0 == -1#2.
Proof.
  simpl.
 reflexivity.
Qed.

Lemma gprod_base : forall e, In e basevect3D -> 
 e *g e =V C[1].
Proof.
  intros e H.
  unfold basevect3D in *.
  simpl In in H.
  intuition; subst; reflexivity.
Qed.

Lemma gprod_ep :  e_p *g e_p =V C[1].
Proof.
  reflexivity.
Qed.


Definition mv1 := [[ e1: 1 , e2: 2 ,  e3: 3 , ep: 4 , em: 5 , e12: 6 , e13: 1 , e1p: 2 , e1m: 3 , e23: 4 , e2p: 5 , e2m: 6 , e3p: 7 , e3m: 8 , epm: 1 , e123: 2 , e12p: 3 , e12m: 4 , e13p: 4 , e13m: 1 , e1pm: 2 , e23p: 1 , e23m: 3 , e2pm: 1 , e3pm: 2 ,  e123p: 1 , e123m: 3 , e12pm: 4 , e13pm: -1 , e23pm: 5 , e123pm: 1 , K: 2 ]].
Definition mv2 := [[ e1: 1 , e2: 5 ,  e3: -1 , ep: 2 , em: 3 , e12: 1 , e13: 5 , e1p: 3 , e1m: 1 , e23: 2 , e2p: -1 , e2m: -2 , e3p: 1 , e3m: 3 , epm: 4 , e123: 2 , e12p: 1 , e12m: 7 , e13p: 3 , e13m: 2 , e1pm: 1 , e23p: 3 , e23m: 2 , e2pm: 4 , e3pm: -2 ,  e123p: 2 , e123m: 5 , e12pm: 1 , e13pm: -1 , e23pm: -5 , e123pm: 2 , K: 3 ]].
Definition e_12 := [[ e1: 0 , e2: 0 ,  e3: 0 , ep: 0 , em: 0 , e12: 1 , e13: 0 , e1p: 0 , e1m: 0 , e23: 0 , e2p:0 , e2m: 0 , e3p: 0 , e3m: 0 , epm: 0 , e123: 0 , e12p: 0 , e12m: 0 , e13p: 0 , e13m: 0 , e1pm: 0 , e23p: 0 , e23m: 0 , e2pm: 0 , e3pm: 0 ,  e123p: 0 , e123m: 0 , e12pm: 0 , e13pm: 0 , e23pm: 0 , e123pm: 0 , K: 0 ]].

Compute (e_12 *s e_12).

Definition Point2CGA (x:point) : vect := x + ((1#2) * ((p2v x) *s (p2v x))) .* e_inf + e_0.

Definition Sphere2CGA (center:point) (radius: Q) := Point2CGA center - ((1#2)*radius*radius) .* e_inf.

Definition Plane2CGA (n: point) (d:Q) := p2v n+d.*e_inf.
(* Definition Plane2CGA (a b c : point) := *)

Definition Midplane2CGA (a b : point) := Point2CGA a - Point2CGA b.

Definition Circle2CGA (S1 S2 : vect ) := S1 ∧ S2.

Definition Line2CGA (P1 P2 : vect) := P1 ∧ P2.

Definition PointPair2CGA (S1 S2 S3 : vect) := S1 ∧ S2 ∧ S3.

Definition OPNSSphere2CGA (p1 p2 p3 p4 : point ) := Point2CGA p1 ∧ Point2CGA p2 ∧ Point2CGA p3 ∧ Point2CGA p4.

Definition OPNSPlane2CGA (p1 p2 p3 : point ) := Point2CGA p1 ∧ Point2CGA p2 ∧ Point2CGA p3 ∧ e_inf.

Definition OPNSCircle2CGA (p1 p2 p3 : point ) := Point2CGA p1 ∧ Point2CGA p2 ∧ Point2CGA p3.

Definition OPNSLine2CGA (p1 p2 : point ) := Point2CGA p1 ∧ Point2CGA p2 ∧ e_inf.

Definition OPNSPointPair2CGA (P1 P2 : vect ) := P1 ∧ P2.

Definition IPNS (V : vect) := fun x:point => V *s (Point2CGA x) == 0. 
Definition OPNS V := fun x:point => V ∧ (Point2CGA x) =V C[0]. 

Axiom Qfield : fparamsProp p.
#[global]
Hint Resolve Qfield : core.

Lemma foo:
forall x y z : Grassmann.vect p 5,
        (x + y)%v *s z =
       (x *s  z +  y *s z)%f.
Proof.
  apply prod_scal_addl.
  apply Qfield.
  Qed.


  Ltac Vfold :=
     change (add p (dim p)) with (addE (vn_eparams p  (dim p))) in *;
     change (Vadd p ) with (addE (vn_eparams p  (dim p))) in *;
     change (Vscal p) with  (scalE (vn_eparams p (dim p))) in *;
     change (Vgenk p) with (E0 (vn_eparams p (dim p))) in *.
  


Lemma point_decomp : forall p : point, exists x y z, 
 p2v p = (x .* e_1 + y .* e_2 + z .* e_3).
 Proof.
   intros.
   destruct p0 as [x [ y [z Hz] ] ].
  exists x.
  exists y.
  exists z.
  destruct Hz.
  simpl.
  unfold K2G.
  simpl.
  unfold e_1.
  unfold e_2.
  unfold e_3.
  unfold e_1.
  unfold Vgen.
  unfold Vscal.
  simpl.
  replace (x*1) with x.
  replace (x*0) with 0.
  replace (y*0) with 0.
  replace (z*0) with 0.
  replace (y*1) with y.
  replace (z*1) with z.
  unfold Vadd.
  simpl.
  f_equal;f_equal;f_equal;repeat f_equal.
(*apply Qfield.*) 
Admitted.


Lemma  point_prodscal_e_inf : forall p : point, (p2v p) *s e_inf == 0.
Proof.
  intros p.
  destruct (point_decomp p) as [x [y [z H] ] ].
  rewrite H.
  simpl.
  ring.
Qed.

Lemma  e_inf_prodscal_point : forall p : point, e_inf *s (p2v p) == 0.
Proof.
  intros p.
  destruct (point_decomp p) as [x [y [z H] ] ].
  rewrite H.
  simpl.
  ring.
Qed.

Lemma  point_prodscal_e_0 : forall p : point, (p2v p) *s e_0 == 0.
Proof.
  intros p.
  destruct (point_decomp p) as [x [y [z H] ] ].
  rewrite H.
  simpl.
  ring.
Qed.

Lemma  e_0_prodscal_point : forall p : point, e_0 *s (p2v p) == 0.
Proof.
  intros p.
  destruct (point_decomp p) as [x [y [z H] ] ].
  rewrite H.
  simpl.
  ring.
Qed.

#[global]
Hint Rewrite prod_scal_addl prod_scal_addr prod_scal_scall prod_scal_scalr : prodscalex .

Ltac prodscal_expand := autorewrite with prodscalex; auto.


Ltac prodsimpl :=
   rewrite ?e_0_prodscal_point, ?point_prodscal_e_0, ?e_inf_prodscal_point, ?point_prodscal_e_inf, 
           ?inner_e_0_e_inf, ?inner_e_inf_e_0, ?inner_e0_null in * by auto;Krm1.

Ltac K2Q:=  change (addK (Clifford.K1 p)) with Qplus in * ;
           change (multK (stype (vn_eparams p (dim p)))) with Qmult in *.
           

(* 
Ltac prodscal_expand := rewrite ?prod_scal_addl, ?prod_scal_addr,
 ?prod_scal_scall, ?prod_scal_scalr by auto.

*)

Lemma square_diff : forall x y, (x-y) *s (x-y) == (x *s x) -2 * (x *s y) + (y *s y).
Proof.
  intros.
  Vfold.
  prodscal_expand.
  K2Q.
  rewrite (prod_scal_sym p Qfield (dim p) l x y).
  ring.
Qed.


Lemma square_point_null_null : forall p q:point, (p2v p - (p2v q)) *s (p2v p - (p2v q)) ==0 -> p - q =V 0%v.
Proof.
  intros p q.
  destruct q as [qx [ qy [qz Hq ] ] ].
  destruct Hq.
  destruct p as [px [ py [pz Hp ] ] ].
  destruct Hp.
  unfold p2v,K2G. simpl.
  intro H.
  ring_simplify in H.
  setoid_replace (pz ^ 2 + -2 * pz * qz + qz ^ 2 + py ^ 2 + -2 * py * qy + qy ^ 2 + px ^ 2 + -2 * px * qx +
  qx ^ 2)%Q with ((pz - qz) ^2 + (py - qy) ^2 + (px - qx)^2)%Q in H by ring.
 set (z := (pz - qz)%Q) in *.
 set (y := (py - qy)%Q) in *.
 set (x := (px - qx)%Q) in *.

  assert (Ha: x == 0  /\ y==0 /\ z==0) by nra.
  destruct  Ha as [Hx [ Hy Hz ] ].
  unfold Veq.
  simpl.
  unfold z in *.
  unfold y in *.
  unfold x in *.
  rewrite Hx, Hy, Hz.
  reflexivity.
Qed.
 


Lemma IPNSPoint : forall (p1 p2:point), IPNS (Point2CGA p1) p2 <-> p1 =V p2.
Proof.
  intros p1 p2.
  unfold IPNS, Point2CGA.
    unfold Vadd.
  Vfold.
  prodscal_expand.
  prodsimpl.
split;intro.
 K2Q.
ring_simplify in H.
(*
assert (T: -2 * (p2v p1 *s p2v p2 + (-1 # 2) * (p2v p1 *s p2v p1) + (-1 # 2) * (p2v p2 *s p2v p2) ) == -2* 0)
 by (rewrite H;ring).
 setoid_replace (-2 * (p2v p1 *s p2v p2 + (-1 # 2) * (p2v p1 *s p2v p1) + (-1 # 2) * (p2v p2 *s p2v p2))) with
   ((((p2v p1) *s (p2v p1)) - 2 * (p2v p1 *s p2v p2) + (p2v p2 *s  p2v p2))%Q)  in T by ring.
  rewrite <- (square_diff (p2v p1) (p2v p2)) in T.
subst.
change (addK (Clifford.K1 p)) with Qplus.
change (multK (stype (vn_eparams p (dim p)))) with Qmult.
setoid_replace (-2*0) with 0 in T by ring.
apply (square_point_null_null p1 p2) in T.
unfold Veq in T.
Check (add_eq_compat p Qfield (dim p) (p1 - p2) 0%v (p2v p2)).
apply  (add_eq_compat p Qfield (dim p) (p1 - p2) 0%v (p2v p2)) in T.
change (add p p) with (Vadd p) in *.
change (Vadd p ) with (addE (vn_eparams p  (dim p))) in *.
Vfold.
Search fparamsProp.
rewrite (addE0l) in T. 
*)

Admitted.





Lemma IPNSSphere : forall (center : point) (r:Q) (x:point),
  IPNS (Sphere2CGA center r) x <-> (x-center) *s (x-center) == r*r.
Proof.
  intros center r x.
  unfold IPNS, Sphere2CGA, Point2CGA.
  Vfold.
  prodscal_expand.
  prodsimpl.
  rewrite prod_scal_sym by auto.
  K2Q.
  split;intro;nra. 
Qed.

Lemma IPNSPlane : forall (n x:point) (d:Q), IPNS (Plane2CGA n d) x <-> p2v x *s p2v n == d.
Proof.
  intros.
  unfold IPNS, Plane2CGA, Point2CGA.
  Vfold.
  prodscal_expand.
  prodsimpl.
  rewrite prod_scal_sym by auto.
  K2Q.
  split;intro;nra. 
Qed.

Lemma IPNSMidplane: forall (a b x: point), IPNS (Midplane2CGA a b) x <-> (x-a) *s (x-a)  == (x-b) *s (x-b).
Proof.
  intros a b x.
  unfold IPNS, Midplane2CGA, Point2CGA.
  Vfold.
  prodscal_expand.
  prodsimpl.

  rewrite (prod_scal_sym) by auto.
  rewrite (prod_scal_sym p Qfield (dim p) l (p2v b) (p2v x)).
  K2Q.
  split;intro;nra. 
Qed.

End CGA3D.