theory Lark
  imports Main
begin

section \<open> Data Structures \<close>

datatype Privilege = EL0 | EL1
datatype Partition = Unsec | Sec

type_synonym Entity_ID = nat
type_synonym SecurityLevel = "Privilege \<times> Partition"

record REG_SCTLR =
  WXN :: bool

record Entity =
  id :: Entity_ID
  security_level :: SecurityLevel

type_synonym Subject = Entity

record Object = Entity +
  urn :: bool
  uwn :: bool
  uxn :: bool
  prn :: bool
  pwn :: bool
  pxn :: bool

type_synonym TA = Subject         (* Trusted Subject *)
type_synonym OT = "Object set"    (* Trusted Objects *)

datatype Operation = Read | Write | Exec | TA_Call TA
type_synonym Request = "Subject \<times> Object \<times> Operation \<times> OT"
datatype Decision = Yes | No

type_synonym ERET_TO_TA = "Object \<Rightarrow> nat"

record F =
  F1 :: "Subject \<Rightarrow> Privilege"
  F2 :: "Subject \<Rightarrow> Partition"
  F3 :: "Object \<Rightarrow> Privilege"
  F4 :: "Object \<Rightarrow> Partition"

record State =
  reqs :: "Request set"
  subjects :: "Entity_ID \<rightharpoonup> Subject"
  objects :: "Entity_ID \<rightharpoonup> Object"
  trusted_objs :: "Object set"


section \<open> Constants \<close>

consts trusted_sub :: "Subject"
consts SCTLR :: REG_SCTLR
consts ta_execution :: "ERET_TO_TA"


section \<open> Utility Functions \<close>

definition is_ta_call_op :: "Operation \<Rightarrow> bool"
  where "is_ta_call_op op \<equiv>
    case op of
      TA_Call ta \<Rightarrow> True |
      _ \<Rightarrow> False"

definition is_ta_call_req :: "Request \<Rightarrow> bool"
  where "is_ta_call_req req \<equiv>
    let op = fst (snd (snd req))
     in
        is_ta_call_op op"

definition is_priv_ge :: "Privilege \<Rightarrow> Privilege \<Rightarrow> bool"
  where "is_priv_ge priv1 priv2 \<equiv>
    (priv1 = priv2) \<or> (priv1 = EL1)"

definition is_part_ge :: "Partition \<Rightarrow> Partition \<Rightarrow> bool"
  where "is_part_ge part1 part2 \<equiv>
    (part1 = part2) \<or> (part1 = Sec)"

definition is_level_ge :: "SecurityLevel \<Rightarrow> SecurityLevel \<Rightarrow> bool"
  where "is_level_ge l1 l2 \<equiv>
    is_priv_ge (fst l1) (fst l2) \<and>
    is_part_ge (snd l1) (snd l2)"

definition is_attr_ge :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  where "is_attr_ge a1 a2 \<equiv>
    (a1 = a2) \<or> (a1 = True)"

definition min_priv :: "Privilege \<Rightarrow> Privilege \<Rightarrow> Privilege"
  where "min_priv priv1 priv2 \<equiv>
    if is_priv_ge priv1 priv2 then
      priv2
    else
      priv1"

value "min_priv EL1 EL0"

definition min_priv_lst :: "Privilege list \<Rightarrow> Privilege"
  where "min_priv_lst privs \<equiv>
    foldl min_priv EL1 privs"

value "min_priv_lst [EL1, EL0, EL1]"

definition obj_id_generator :: "State \<Rightarrow> Entity_ID option"
  where "obj_id_generator s \<equiv>
    if (\<exists> x. (objects s) x = None) then
      Some (SOME x. (objects s) x = None)
    else
      None"

definition get_ta_from_op :: "Operation \<Rightarrow> TA option"
  where "get_ta_from_op op \<equiv>
    case op of
      TA_Call ta \<Rightarrow> Some ta |
      _ \<Rightarrow> None"


section \<open> Basic Elements \<close>

definition dominance :: "SecurityLevel \<Rightarrow> SecurityLevel \<Rightarrow> bool" ("(_ \<succeq> _)")
  where "dominance l1 l2 \<equiv>
    is_priv_ge (fst l1) (fst l2) \<and>
    is_part_ge (snd l1) (snd l2)"

definition non_dominance :: "SecurityLevel \<Rightarrow> SecurityLevel \<Rightarrow> bool" ("(_ |\<succeq> _)")
  where "non_dominance l1 l2 \<equiv>
    \<not> (dominance l1 l2)"

definition f1 :: "Subject \<Rightarrow> Privilege"
  where "f1 sub \<equiv>
    fst (security_level sub)"

definition f2 :: "Object \<Rightarrow> Privilege"
  where "f2 obj \<equiv>
    fst (security_level obj)"

definition f3 :: "Subject \<Rightarrow> Partition"
  where "f3 sub \<equiv>
    snd (security_level sub)"

definition f4 :: "Object \<Rightarrow> Partition"
  where "f4 obj \<equiv>
    snd (security_level obj)"

definition fs :: "Subject \<Rightarrow> SecurityLevel"
  where "fs sub \<equiv>
    security_level sub"

definition fo :: "Object \<Rightarrow> SecurityLevel"
  where "fo obj \<equiv>
    security_level obj"

definition is_trusted_subject :: "Subject \<Rightarrow> bool"
  where "is_trusted_subject sub \<equiv>
    sub = trusted_sub"

definition is_trusted_object :: "OT \<Rightarrow> Object \<Rightarrow> bool"
  where "is_trusted_object t_objs obj \<equiv>
    obj \<in> t_objs"

definition is_reuqest_secure :: "Request \<Rightarrow> bool"
  where "is_reuqest_secure req \<equiv>
    let sub = fst req;
        obj = fst (snd req)
     in sub = trusted_sub \<or>
        ((security_level sub) \<succeq> (security_level obj)) \<and>
         ((security_level obj) \<succeq> (security_level sub))"

definition is_state_secure :: "State \<Rightarrow> bool"
  where "is_state_secure s \<equiv>
    \<forall> req \<in> (reqs s). is_reuqest_secure req"


section \<open> Access Control Policies \<close>

(* BLP ss-property：Read-down *)
definition blp_ss_property :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "blp_ss_property sub obj \<equiv>
    if ((security_level sub) \<succeq> (security_level obj)) then
      True
    else
      False"

(* BLP *-property：Write-up *)
definition blp_star_property :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "blp_star_property sub obj \<equiv>
    if ((security_level obj) \<succeq> (security_level sub)) then
      True
    else
      False"

(* Biba ss-property：Read-up *)
definition biba_ss_property :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "biba_ss_property sub obj \<equiv>
    if ((security_level obj) \<succeq> (security_level sub)) then
      True
    else
      False"

(* Biba *-property：Write-down *)
definition biba_star_property :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "biba_star_property sub obj \<equiv>
    if ((security_level sub) \<succeq> (security_level obj)) then
      True
    else
      False"

definition urn_policy :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "urn_policy sub obj \<equiv>
    if (f1 sub) = EL0 \<and> (urn obj) = True then
      False
    else
      True"

definition uwn_policy :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "uwn_policy sub obj \<equiv>
    if (f1 sub) = EL0 \<and> (uwn obj) = True then
      False
    else
      True"

definition uxn_policy :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "uxn_policy sub obj \<equiv>
    if (f1 sub) = EL0 \<and> (uxn obj) = True then
      False
    else
      True"

definition prn_policy :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "prn_policy sub obj \<equiv>
    if (f1 sub) \<noteq> EL0 \<and> (prn obj) = True then
      False
    else
      True"

definition pwn_policy :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "pwn_policy sub obj \<equiv>
    if (f1 sub) \<noteq> EL0 \<and> (pwn obj) = True then
      False
    else
      True"

definition pxn_policy :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "pxn_policy sub obj \<equiv>
    if (f1 sub) \<noteq> EL0 \<and> (pxn obj) = True then
      False
    else
      True"

definition wxn_policy :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "wxn_policy sub obj \<equiv>
    if (WXN SCTLR) \<and>
       ((\<not> uwn obj) \<or>
        (\<not> pwn obj) \<and> (f1 sub) \<noteq> EL0) then
      False
    else
      True"

definition idc_policy :: "Object \<Rightarrow> Object \<Rightarrow> bool"
  where "idc_policy buf shadow_buf \<equiv>
    is_attr_ge (prn shadow_buf) (prn buf) \<and>
    is_attr_ge (pwn shadow_buf) (pwn buf) \<and>
    is_attr_ge (pxn shadow_buf) (pxn buf) \<and>
    is_attr_ge (urn shadow_buf) (urn buf) \<and>
    is_attr_ge (uwn shadow_buf) (uwn buf) \<and>
    is_attr_ge (uxn shadow_buf) (uxn buf)"


section \<open> Access Control Rules \<close>

definition is_readable :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "is_readable sub obj \<equiv>
    if (f1 sub) = EL0 then
      urn_policy sub obj
    else
      prn_policy sub obj"

definition is_writable :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "is_writable sub obj \<equiv>
    if (f1 sub) = EL0 then
      uwn_policy sub obj
    else
      pwn_policy sub obj"

definition is_executable :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "is_executable sub obj \<equiv>
    if (f1 sub) = EL0 then
      uxn_policy sub obj
    else
      pxn_policy sub obj"

definition rule_read_normal :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "rule_read_normal sub obj \<equiv>
    blp_ss_property sub obj \<and>
    biba_ss_property sub obj \<and>
    is_readable sub obj"

definition rule_read_trusted :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "rule_read_trusted sub obj \<equiv>
    is_readable sub obj"

definition rule_write_normal :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "rule_write_normal sub obj \<equiv>
    blp_star_property sub obj \<and>
    biba_star_property sub obj \<and>
    is_writable sub obj"

definition rule_write_trusted :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "rule_write_trusted sub obj \<equiv>
    is_writable sub obj"

definition rule_exec_normal :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "rule_exec_normal sub obj \<equiv>
    rule_read_normal sub obj \<and>
    is_executable sub obj \<and>
    wxn_policy sub obj"

definition rule_exec_trusted :: "Subject \<Rightarrow> Object \<Rightarrow> bool"
  where "rule_exec_trusted sub obj \<equiv>
    is_readable sub obj \<and>
    is_executable sub obj \<and>
    wxn_policy sub obj"


section \<open> Access Methods \<close>

definition normal_subject_access :: "State \<Rightarrow> Request \<Rightarrow> State \<times> Decision"
  where "normal_subject_access s req \<equiv>
    let sub = fst req;
        obj = fst (snd req);
        op = fst (snd (snd req));
        s' = s\<lparr> reqs := insert req (reqs s) \<rparr>
     in
       if op = Read \<and> (rule_read_normal sub obj) then
          (s', Yes)
       else if op = Write \<and> (rule_write_normal sub obj) then
          (s', Yes)
       else if op = Exec \<and> (rule_exec_normal sub obj) then
          (s', Yes)
       else
          (s, No)"

definition trusted_subject_access :: "State \<Rightarrow> Request \<Rightarrow> State \<times> Decision"
  where "trusted_subject_access s req \<equiv>
    let sub = fst req;
        obj = fst (snd req);
        op = fst (snd (snd req));
        s' = s\<lparr> reqs := insert req (reqs s) \<rparr>
     in
        if op = Read \<and> (rule_read_trusted sub obj) then
          (s', Yes)
        else if op = Write \<and> (rule_write_trusted sub obj) then
          (s', Yes)
        else if op = Exec \<and> (rule_exec_trusted sub obj) then
          (s', Yes)
       else
          (s, No)"

definition do_access :: "State \<Rightarrow> Request \<Rightarrow> State"
  where "do_access s req \<equiv>
    let sub = fst req;
        obj = fst (snd req);
        t_objs = snd (snd (snd req))
     in
        if (is_trusted_subject sub) \<and> (is_trusted_object t_objs obj) then
          fst (trusted_subject_access s req)
        else
          fst (normal_subject_access s req)"

subsection \<open> Direct Access Methods \<close>

definition do_read :: "State \<Rightarrow> Subject \<Rightarrow> Object \<Rightarrow> State \<times> Decision"
  where "do_read s sub obj \<equiv>
    let t_objs = trusted_objs s;
        req = (sub, obj, Read, t_objs);
        s' = s\<lparr> reqs := insert req (reqs s) \<rparr>
     in
        if (is_trusted_subject sub) \<and>
           (is_trusted_object t_objs obj) then
          if (rule_read_trusted sub obj) then
            (s', Yes)
          else
            (s, No)
        else
          if (rule_read_normal sub obj) then
            (s', Yes)
          else
            (s, No)"

definition do_write :: "State \<Rightarrow> Subject \<Rightarrow> Object \<Rightarrow> State \<times> Decision"
  where "do_write s sub obj \<equiv>
    let t_objs = trusted_objs s;
        req = (sub, obj, Write, t_objs);
        s' = s\<lparr> reqs := insert req (reqs s) \<rparr>
     in
        if (is_trusted_subject sub) \<and>
           (is_trusted_object t_objs obj) then
          if (rule_write_trusted sub obj) then
            (s', Yes)
          else
            (s, No)
        else
          if (rule_write_normal sub obj) then
            (s', Yes)
          else
            (s, No)"

definition do_exec :: "State \<Rightarrow> Subject \<Rightarrow> Object \<Rightarrow> State \<times> Decision"
  where "do_exec s sub obj \<equiv>
    let t_objs = trusted_objs s;
        req = (sub, obj, Exec, t_objs);
        s' = s\<lparr> reqs := insert req (reqs s) \<rparr>
     in
        if (is_trusted_subject sub) \<and>
           (is_trusted_object t_objs obj) then
          if (rule_exec_trusted sub obj) then
            (s', Yes)
          else
            (s, No)
        else
          if (rule_exec_normal sub obj) then
            (s', Yes)
          else
            (s, No)"

subsection \<open> Inter-domain Communication \<close>

definition inv_object :: "Object"
  where "inv_object \<equiv>
    \<lparr> id = 0, security_level = (EL0, Unsec),
      urn = True, uwn = True, uxn = True,
      prn = True, pwn = True, pxn = True \<rparr>"

definition ta_enter :: "State \<Rightarrow> Subject \<Rightarrow> Object \<Rightarrow> Subject \<Rightarrow> State \<times> Object option"
  where "ta_enter s client buf ta \<equiv>
    let objs = objects s;
        t_objs = trusted_objs s;
        priv = min_priv_lst [(f2 buf), (f1 client), (f1 ta)];
        new_id = obj_id_generator s;
        shadow_buf = buf\<lparr> id := (the new_id), security_level := (priv, Sec),
                                pxn := True, uxn := True \<rparr>;
        new_objs = objs((the new_id) := Some shadow_buf);
        new_t_objs = t_objs \<union> {buf, shadow_buf};
        s1 = s\<lparr> objects := new_objs, trusted_objs := new_t_objs \<rparr>;
        (s2, d2) = do_read s1 trusted_sub buf;
        (s3, d3) = do_write s2 trusted_sub shadow_buf;
        objs2 = objects s3;
        t_objs2 = trusted_objs s3;
        new_objs2 = objs2((the new_id) := None);
        new_t_objs2 = t_objs2 - {buf, shadow_buf};
        s4 = s3\<lparr> trusted_objs := new_t_objs2 \<rparr>
     in
        if new_id \<noteq> None \<and> d2 = Yes \<and> d3 = Yes then
          (s4, Some shadow_buf)
        else
          (s, None)"

definition ta_exit :: "State \<Rightarrow> Object \<Rightarrow> Object \<Rightarrow> State"
  where "ta_exit s buf shadow_buf \<equiv>
    let obj_id = id shadow_buf;
        objs = objects s;
        t_objs = trusted_objs s;
        new_objs = objs(obj_id := Some shadow_buf);
        new_t_objs = t_objs \<union> {buf, shadow_buf};
        s1 = s\<lparr> trusted_objs := new_t_objs \<rparr>;
        (s2, d2) = do_read s1 trusted_sub shadow_buf;
        (s3, d3) = do_write s2 trusted_sub buf;
        objs2 = objects s3;
        t_objs2 = trusted_objs s3;
        new_objs2 = objs2(obj_id := None);
        new_t_objs2 = t_objs2 - {buf, shadow_buf};
        s4 = s3\<lparr> objects := new_objs2, trusted_objs := new_t_objs2 \<rparr>
     in
        s4"

definition ta_call :: "State \<Rightarrow> Subject \<Rightarrow> Object \<Rightarrow> Subject \<Rightarrow> State \<times> Decision"
  where "ta_call s client buf ta \<equiv>
    let (s1, shadow_buf) = ta_enter s client buf ta;
        _ = ta_execution (the shadow_buf);
        s2 = ta_exit s1 buf (the shadow_buf)
     in
        if shadow_buf \<noteq> None \<and>
           idc_policy buf (the shadow_buf) then
          (s2, Yes)
        else
          (s, No)"

subsection \<open> Transition Function \<close>

definition transition :: "State \<Rightarrow> Request \<Rightarrow> State \<times> Decision"
  where "transition s req \<equiv>
    case req of
      (sub, obj, Read, _) \<Rightarrow> do_read s sub obj |
      (sub, obj, Write, _) \<Rightarrow> do_write s sub obj |
      (sub, obj, Exec, _) \<Rightarrow> do_exec s sub obj |
      (sub, obj, TA_Call ta, _) \<Rightarrow> ta_call s sub obj ta"


section \<open> Security Properties \<close>

definition buffers_in_trusted_set :: "State \<Rightarrow> Request \<Rightarrow> bool"
  where "buffers_in_trusted_set s req \<equiv>
    let client = fst req;
        buf = fst (snd req);
        op = fst (snd (snd req));
        ta = get_ta_from_op op;
        (s1, shadow_buf) = ta_enter s client buf (the ta)
     in
        if (shadow_buf \<noteq> None) then
          buf \<in> trusted_objs s1 \<and>
          (the shadow_buf) \<in> trusted_objs s1
        else
          True"

definition confidentiality :: "State \<Rightarrow> Request \<Rightarrow> bool"
  where "confidentiality s req \<equiv>
    let sub = fst req;
        obj = fst (snd req);
        op = fst (snd (snd req));
        t_objs = snd (snd (snd req))
     in
        if (is_trusted_subject sub) \<and> (is_trusted_object t_objs obj) then
          True
        else if op = Read \<or> op = Exec then
          blp_ss_property sub obj
        else if op = Write then
          blp_star_property sub obj
        else
          False"

definition integrity :: "State \<Rightarrow> Request \<Rightarrow> bool"
  where "integrity s req \<equiv>
    let sub = fst req;
        obj = fst (snd req);
        op = fst (snd (snd req));
        t_objs = snd (snd (snd req))
     in
        if (is_trusted_subject sub) \<and> (is_trusted_object t_objs obj) then
          True
        else if op = Read \<or> op = Exec then
          biba_ss_property sub obj
        else if op = Write then
          biba_star_property sub obj
        else
          False"

definition attribute_constraints :: "State \<Rightarrow> Request \<Rightarrow> bool"
  where "attribute_constraints s req \<equiv>
    let sub = fst req;
        obj = fst (snd req);
        op = fst (snd (snd req))
     in
        if op = Read then
          (prn_policy sub obj) \<and> (urn_policy sub obj)
        else if op = Write then
          (pwn_policy sub obj) \<and> (uwn_policy sub obj)
        else if op = Exec then
          (pxn_policy sub obj) \<and> (uxn_policy sub obj)
        else
          False"

definition prop_isolation_r :: "Request \<Rightarrow> bool"
  where "prop_isolation_r r \<equiv> \<forall> d s s' b.
    (s', d) = transition s r \<and>
    b \<in> (reqs s') - (reqs s) \<longrightarrow>
    (confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"

definition prop_isolation :: "bool"
  where "prop_isolation \<equiv> \<forall> r d s s' b.
    (s', d) = transition s r \<and>
    b \<in> (reqs s') - (reqs s) \<longrightarrow>
    (confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"

definition equiv_sub_attr :: "Subject option \<Rightarrow> Subject option \<Rightarrow> bool"
  where "equiv_sub_attr sub1 sub2 \<equiv>
    if sub1 = None \<and> sub2 = None then
      True
    else if sub1 \<noteq> None \<and> sub2 \<noteq> None then
      let ts1 = the sub1;
          ts2 = the sub2
        in
          fs ts1 = fs ts2
    else
      False"

definition equiv_obj_attr :: "Object option \<Rightarrow> Object option \<Rightarrow> bool"
  where "equiv_obj_attr obj1 obj2 \<equiv>
    if obj1 = None \<and> obj2 = None then
      True
    else if obj1 \<noteq> None \<and> obj2 \<noteq> None then
      let to1 = the obj1;
          to2 = the obj2
        in
          fo to1 = fo to2 \<and>
          prn to1 = prn to2 \<and> pwn to1 = pwn to2 \<and> pxn to1 = pxn to2 \<and>
          urn to1 = urn to2 \<and> uwn to1 = uwn to2 \<and> uxn to1 = uxn to2
    else
      False"

definition noninterference_r :: "Request \<Rightarrow> bool"
  where "noninterference_r r \<equiv> \<forall> d s s'.
    (s', d) = transition s r \<longrightarrow>
    (\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
    (\<forall> j. equiv_obj_attr ((objects s) j) ((objects s') j))"

definition noninterference :: "bool"
  where "noninterference \<equiv> \<forall> r d s s'.
    (s', d) = transition s r \<longrightarrow>
    (\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
    (\<forall> j. equiv_obj_attr ((objects s) j) ((objects s') j))"


section \<open> Security Proofs \<close>

subsection \<open> Auxiliary Lemmas \<close>

lemma equiv_sub_attr_transitive :
  "\<forall> sub1 sub2 sub3.
     equiv_sub_attr sub1 sub2 \<and> equiv_sub_attr sub2 sub3 \<longrightarrow>
     equiv_sub_attr sub1 sub3"
  using equiv_sub_attr_def
  by auto

lemma equiv_obj_attr_transitive :
  "\<forall> sub1 sub2 sub3.
     equiv_obj_attr obj1 obj2 \<and> equiv_obj_attr obj2 obj3 \<longrightarrow>
     equiv_obj_attr obj1 obj3"
  using equiv_obj_attr_def
  by auto

lemma do_read_reqs :
  "\<forall> s s' sub obj d.
   (s', d) = do_read s sub obj \<longrightarrow>
   (reqs s') - (reqs s) \<subseteq> {(sub, obj, Read, trusted_objs s)}"
proof -
  {
    fix s s' sub obj d
    assume a0: "(s', d) = do_read s sub obj"
    let ?req = "(sub, obj, Read, trusted_objs s)"
    have "(reqs s') - (reqs s) \<subseteq> {?req}"
    proof(cases "s' = s")
      assume b0: "s' = s"
      then show ?thesis by simp
    next
      assume b0: "s' \<noteq> s"
      have b1: "s' = s\<lparr> reqs := insert ?req (reqs s) \<rparr>"
        using a0 b0 fst_conv unfolding do_read_def
        by (smt (verit, best))
      then show ?thesis
        by auto
    qed
  }
  then show ?thesis
    by simp
qed

lemma do_write_reqs :
  "\<forall> s s' sub obj d.
   (s', d) = do_write s sub obj \<longrightarrow>
   (reqs s') - (reqs s) \<subseteq> {(sub, obj, Write, trusted_objs s)}"
proof -
  {
    fix s s' sub obj d
    assume a0: "(s', d) = do_write s sub obj"
    let ?req = "(sub, obj, Write, trusted_objs s)"
    have "(reqs s') - (reqs s) \<subseteq> {?req}"
    proof(cases "s' = s")
      assume b0: "s' = s"
      then show ?thesis by simp
    next
      assume b0: "s' \<noteq> s"
      have b1: "s' = s\<lparr> reqs := insert ?req (reqs s) \<rparr>"
        using a0 b0 fst_conv unfolding do_write_def
        by (smt (verit, best))
      then show ?thesis
        by auto
    qed
  }
  then show ?thesis
    by simp
qed

lemma do_exec_reqs :
  "\<forall> s s' sub obj d.
   (s', d) = do_exec s sub obj \<longrightarrow>
   (reqs s') - (reqs s) \<subseteq> {(sub, obj, Exec, trusted_objs s)}"
proof -
  {
    fix s s' sub obj d
    assume a0: "(s', d) = do_exec s sub obj"
    let ?req = "(sub, obj, Exec, trusted_objs s)"
    have "(reqs s') - (reqs s) \<subseteq> {?req}"
    proof(cases "s' = s")
      assume b0: "s' = s"
      then show ?thesis by simp
    next
      assume b0: "s' \<noteq> s"
      have b1: "s' = s\<lparr> reqs := insert ?req (reqs s) \<rparr>"
        using a0 b0 fst_conv unfolding do_exec_def
        by (smt (verit, best))
      then show ?thesis
        by auto
    qed
  }
  then show ?thesis
    by simp
qed

lemma do_read_req_sec :
  "\<forall> s s' sub obj d req.
   (s', d) = do_read s sub obj \<and>
   req = (sub, obj, Read, trusted_objs s) \<and>
   d = Yes \<longrightarrow> 
   (confidentiality s' req \<and> integrity s' req \<and> attribute_constraints s' req)"
proof -
  {
    fix s s' d sub obj req
    assume a0: "(s', d) = do_read s sub obj"
    assume a1: "req = (sub, obj, Read, trusted_objs s)"
    assume a2: "d = Yes"

    let ?t_objs = "trusted_objs s"
    have a3: "s' = s\<lparr> reqs := insert req (reqs s) \<rparr>"
      using a0 a1 a2 do_read_def
      by (smt (verit) Decision.distinct(1) Pair_inject State.fold_congs(1))
    have a5: "trusted_objs s' = trusted_objs s"
      using a3 by auto
    have "(confidentiality s' req \<and> integrity s' req \<and> attribute_constraints s' req)"
    proof(cases "(is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj)")
      assume b0: "(is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj)"
      then show ?thesis
        using a0 a1 a2 a5 confidentiality_def integrity_def attribute_constraints_def
              do_read_def is_readable_def rule_read_normal_def rule_read_trusted_def
              prn_policy_def urn_policy_def
              Decision.distinct(1) Operation.distinct(1) fst_conv
        by force
    next
      assume b0: "\<not> ((is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj))"
      then show ?thesis
        using a0 a1 a2 a5 b0 confidentiality_def integrity_def attribute_constraints_def
              do_read_def is_readable_def rule_read_normal_def rule_read_trusted_def
              prn_policy_def urn_policy_def
              Decision.distinct(1) Operation.distinct(1) fst_conv snd_conv
        by (smt (verit) Operation.distinct(7))
    qed
  }
  then show ?thesis
    by blast
qed

lemma do_write_req_sec :
  "\<forall> s s' sub obj d req.
   (s', d) = do_write s sub obj \<and>
   req = (sub, obj, Write, trusted_objs s) \<and>
   d = Yes \<longrightarrow> 
   (confidentiality s' req \<and> integrity s' req \<and> attribute_constraints s' req)"
proof -
  {
    fix s s' d sub obj req
    assume a0: "(s', d) = do_write s sub obj"
    assume a1: "req = (sub, obj, Write, trusted_objs s)"
    assume a2: "d = Yes"

    let ?t_objs = "trusted_objs s"
    have a3: "s' = s\<lparr> reqs := insert req (reqs s) \<rparr>"
      using a0 a1 a2 do_write_def
      by (smt (verit) Decision.distinct(1) Pair_inject State.fold_congs(1))
    have a5: "trusted_objs s' = trusted_objs s"
      using a3 by auto
    have "(confidentiality s' req \<and> integrity s' req \<and> attribute_constraints s' req)"
    proof(cases "(is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj)")
      assume b0: "(is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj)"
      then show ?thesis
        using a0 a1 a2 a5 confidentiality_def integrity_def attribute_constraints_def
              do_write_def is_writable_def rule_write_normal_def rule_write_trusted_def
              pwn_policy_def uwn_policy_def
              Decision.distinct(1) Operation.distinct(1) fst_conv
        by force
    next
      assume b0: "\<not> ((is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj))"
      then show ?thesis
        using a0 a1 a2 a5 b0 confidentiality_def integrity_def attribute_constraints_def
              do_write_def is_writable_def rule_write_normal_def rule_write_trusted_def
              pwn_policy_def uwn_policy_def
              Decision.distinct(1) Operation.distinct(1) fst_conv snd_conv
        by (smt (verit) Operation.distinct(7))
    qed
  }
  then show ?thesis
    by blast
qed

lemma do_read_req_not_empty_sec :
  "\<forall> s s' sub obj d req.
   (s', d) = do_read s sub obj \<and>
   req = (sub, obj, Read, trusted_objs s) \<and>
   (reqs s' - reqs s) \<noteq> {} \<longrightarrow> 
   (confidentiality s' req \<and> integrity s' req \<and> attribute_constraints s' req)"
proof -
  {
    fix s s' sub obj d req
    assume a0: "(s', d) = do_read s sub obj"
    assume a1: "req = (sub, obj, Read, trusted_objs s)"
    assume a2: "(reqs s' - reqs s) \<noteq> {}"

    have b0: "s' \<noteq> s"
      using a2 by blast
    have b1: "d = Yes"
      using a0 b0 fst_conv snd_conv do_read_def
      by (smt (verit, ccfv_threshold)) 
    have "(confidentiality s' req \<and> integrity s' req \<and> attribute_constraints s' req)"
      using a0 a1 b1 do_read_req_sec by simp
  }
  then show ?thesis
    by blast
qed

lemma do_write_req_not_empty_sec :
  "\<forall> s s' sub obj d req.
   (s', d) = do_write s sub obj \<and>
   req = (sub, obj, Write, trusted_objs s) \<and>
   (reqs s' - reqs s) \<noteq> {} \<longrightarrow> 
   (confidentiality s' req \<and> integrity s' req \<and> attribute_constraints s' req)"
proof -
  {
    fix s s' sub obj d req
    assume a0: "(s', d) = do_write s sub obj"
    assume a1: "req = (sub, obj, Write, trusted_objs s)"
    assume a2: "(reqs s' - reqs s) \<noteq> {}"

    have b0: "s' \<noteq> s"
      using a2 by blast
    have b1: "d = Yes"
      using a0 b0 fst_conv snd_conv do_write_def
      by (smt (verit, ccfv_threshold)) 
    have "(confidentiality s' req \<and> integrity s' req \<and> attribute_constraints s' req)"
      using a0 a1 b1 do_write_req_sec by simp
  }
  then show ?thesis
    by blast
qed

lemma do_read_persist :
  "\<forall> s s' sub obj d.
   (s', d) = do_read s sub obj \<longrightarrow>
   (subjects s') = (subjects s) \<and>
   (objects s') = (objects s) \<and>
   (trusted_objs s') = (trusted_objs s)"
  unfolding do_read_def
  by (smt (verit, ccfv_threshold) State.select_convs(2) State.select_convs(3)
      State.select_convs(4) State.surjective State.update_convs(1) fst_eqD) 

lemma do_write_persist :
  "\<forall> s s' sub obj d.
   (s', d) = do_write s sub obj \<longrightarrow>
   (subjects s') = (subjects s) \<and>
   (objects s') = (objects s) \<and>
   (trusted_objs s') = (trusted_objs s)"
  unfolding do_write_def
  by (smt (verit, best) State.select_convs(2) State.select_convs(3)
      State.select_convs(4) State.surjective State.update_convs(1) fst_eqD)

lemma ta_enter_helper :
  "\<forall> s s' s1 s2 d1 d2 buf shadow_buf ca ta.
    (s', shadow_buf) = ta_enter s ca buf ta \<and>
    s' \<noteq> s \<longrightarrow>
    shadow_buf \<noteq> None"
proof -
  {
    fix s s' buf shadow_buf ca ta
    assume a0: "(s', shadow_buf) = ta_enter s ca buf ta"
    assume a1: "s' \<noteq> s"
    have "shadow_buf \<noteq> None"
      using a0 a1 fst_conv snd_conv unfolding ta_enter_def
      by (smt (verit, del_insts) case_prod_beta option.discI)
  }
  then show ?thesis
    by blast
qed

lemma ta_enter_helper2:
  "\<forall> s s' s1 s2 d1 d2 buf shadow_buf ca ta.
    (s', shadow_buf) = ta_enter s ca buf ta \<and>
    shadow_buf \<noteq> None \<longrightarrow>
    s' \<noteq> s"
proof -
  {
    fix s s' buf shadow_buf ca ta
    assume a0: "(s', shadow_buf) = ta_enter s ca buf ta"
    assume a1: "shadow_buf \<noteq> None"

    let ?objs = "objects s"
    let ?t_objs = "trusted_objs s"
    let ?priv = "min_priv_lst [(f2 buf), (f1 ca), (f1 ta)]"
    let ?new_id = "obj_id_generator s"
    let ?shadow_buf = "buf\<lparr> id := (the ?new_id), security_level := (?priv, Sec),
                            pxn := True, uxn := True \<rparr>"
    let ?new_objs = "?objs((the ?new_id) := Some ?shadow_buf)"
    let ?new_t_objs = "?t_objs \<union> {buf, ?shadow_buf}"
    let ?s1 = "s\<lparr> objects := ?new_objs, trusted_objs := ?new_t_objs \<rparr>"
    let ?rst2  = "do_read ?s1 trusted_sub buf"
    let ?s2 = "fst ?rst2"
    let ?d2 = "snd ?rst2"
    let ?rst3  = "do_write ?s2 trusted_sub ?shadow_buf"
    let ?s3 = "fst ?rst3"
    let ?d3 = "snd ?rst3"
    let ?objs2 = "objects ?s3"
    let ?t_objs2 = "trusted_objs ?s3"
    let ?new_objs2 = "?objs2((the ?new_id) := None)"
    let ?new_t_objs2 = "?t_objs2 - {buf, ?shadow_buf}"
    let ?s4 = "?s3\<lparr> trusted_objs := ?new_t_objs2 \<rparr>"

    have b1: "s' = ?s4"
      using a0 a1 fst_conv snd_conv unfolding ta_enter_def
      by (smt (verit) State.fold_congs(3) State.fold_congs(4) case_prod_conv prod.collapse)
    have b2: "(the shadow_buf) = ?shadow_buf"
      using a0 a1 fst_conv snd_conv unfolding ta_enter_def
      by (smt (z3) case_prod_beta not_None_eq option.collapse option.inject)
    have b3: "?new_id \<noteq> None"
      using a0 a1 Pair_inject unfolding ta_enter_def
      by fastforce

    have b4: "((objects s) (the ?new_id)) = None"
      using b3 obj_id_generator_def
      by (metis (mono_tags, lifting) exE_some option.sel)
    have b5: "((objects s) (id (the shadow_buf))) = None"
      using b2 b4 by auto
    have b6: "((objects ?s1) (id (the shadow_buf))) \<noteq> None"
      using b2 by simp

    have b7: "(objects ?s1) = (objects ?s2)"
      using fst_conv do_read_persist
      by (smt (verit, best) surj_pair) 
    have b8: "(objects ?s3) = (objects ?s2)"
      using fst_conv do_write_persist
      by (smt (verit, best) surj_pair)
    have b9: "(objects ?s4) = (objects ?s3)"
      by simp

    have b10: "s' \<noteq> s"
      using b1 b4 b5 b6 b7 b8 b9
      by metis
  }
  then show ?thesis
    by blast
qed

subsection \<open> Operations satisfy isolation security \<close>

lemma do_read_isolation :
  "\<forall> s s' d b sub obj.
    (s', d) = do_read s sub obj \<and>
    b \<in> (reqs s') - (reqs s) \<longrightarrow>
    (confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
proof -
  {
    fix s s' d b sub obj
    assume a0: "(s', d) = do_read s sub obj"
    assume a1: "b \<in> (reqs s') - (reqs s)"
    let ?t_objs = "trusted_objs s"
    let ?req = "(sub, obj, Read, ?t_objs)"
    have a3: "s' = s \<or> s' = s\<lparr> reqs := insert ?req (reqs s) \<rparr>"
      using a0 do_read_def
      by (smt (verit) State.fold_congs(1) prod.inject)
    have a4: "(reqs s') - (reqs s) = {} \<or> (reqs s') - (reqs s) = {?req}"
      using a3 by auto
    have a5: "trusted_objs s' = trusted_objs s"
      using a3 by auto
    have "(confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
    proof(cases "(is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj)")
      assume b0: "(is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj)"
      then show ?thesis
        using a0 a1 a4 a5 confidentiality_def integrity_def attribute_constraints_def
              do_read_def is_readable_def rule_read_normal_def rule_read_trusted_def
              prn_policy_def urn_policy_def
        by (smt (verit, del_insts) Diff_eq_empty_iff Diff_subset fst_conv insert_iff
            mem_Collect_eq set_diff_eq snd_conv )
    next
      assume b0: "\<not> ((is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj))"
      then show ?thesis
        using a0 a1 a4 a5 b0 confidentiality_def integrity_def attribute_constraints_def
              do_read_def is_readable_def rule_read_normal_def rule_read_trusted_def
              prn_policy_def urn_policy_def
        by (smt (verit) Diff_cancel empty_iff fst_conv insertE snd_conv)
    qed
  }
  then show ?thesis
    by blast
qed

lemma do_read_isolation_r :
  "prop_isolation_r (sub, obj, Read, t_objs)"
  using prop_isolation_r_def transition_def do_read_isolation
  by (metis (mono_tags, lifting) Operation.simps(14) old.prod.case)

lemma do_write_isolation :
  "\<forall> s s' d b sub obj.
    (s', d) = do_write s sub obj \<and>
    b \<in> (reqs s') - (reqs s) \<longrightarrow>
    (confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
proof -
  {
    fix s s' d b sub obj
    assume a0: "(s', d) = do_write s sub obj"
    assume a1: "b \<in> (reqs s') - (reqs s)"
    let ?t_objs = "trusted_objs s"
    let ?req = "(sub, obj, Write, ?t_objs)"
    have a3: "s' = s \<or> s' = s\<lparr> reqs := insert ?req (reqs s) \<rparr>"
      using a0 do_write_def
      by (smt (verit) State.fold_congs(1) prod.inject)
    have a4: "(reqs s') - (reqs s) = {} \<or> (reqs s') - (reqs s) = {?req}"
      using a3 by auto
    have a5: "trusted_objs s' = trusted_objs s"
      using a3 by auto
    have "(confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
    proof(cases "(is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj)")
      assume b0: "(is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj)"
      then show ?thesis
        using a0 a1 a4 a5 confidentiality_def integrity_def attribute_constraints_def
              do_write_def is_writable_def rule_write_normal_def rule_write_trusted_def
              pwn_policy_def uwn_policy_def
        by (smt (verit, ccfv_threshold) Diff_cancel Operation.distinct(1)
            empty_iff fst_eqD insertE snd_eqD)
    next
      assume b0: "\<not> ((is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj))"
      then show ?thesis
        using a0 a1 a4 a5 b0 confidentiality_def integrity_def attribute_constraints_def
              do_write_def is_writable_def rule_write_normal_def rule_write_trusted_def
              pwn_policy_def uwn_policy_def
        by (smt (verit) Diff_cancel Operation.distinct(1) Operation.distinct(7)
            empty_iff fst_eqD insertE snd_eqD)
    qed
  }
  then show ?thesis
    by blast
qed

lemma do_write_isolation_r :
  "prop_isolation_r (sub, obj, Write, t_objs)"
  using prop_isolation_r_def transition_def do_write_isolation
  by (metis (mono_tags, lifting) Operation.simps(15) old.prod.case)

lemma do_exec_isolation :
  "\<forall> s s' d b sub obj.
    (s', d) = do_exec s sub obj \<and>
    b \<in> (reqs s') - (reqs s) \<longrightarrow>
    (confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
proof -
  {
    fix s s' d b sub obj
    assume a0: "(s', d) = do_exec s sub obj"
    assume a1: "b \<in> (reqs s') - (reqs s)"

    let ?t_objs = "trusted_objs s"
    let ?req = "(sub, obj, Exec, ?t_objs)"
    have a3: "s' = s \<or> s' = s\<lparr> reqs := insert ?req (reqs s) \<rparr>"
      using a0 do_exec_def
      by (smt (verit) State.fold_congs(1) prod.inject)
    have a4: "(reqs s') - (reqs s) = {} \<or> (reqs s') - (reqs s) = {?req}"
      using a3 by auto
    have a5: "trusted_objs s' = trusted_objs s"
      using a3 by auto
    have "(confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
    proof(cases "(is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj)")
      assume b0: "(is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj)"
      then show ?thesis
        using a0 a1 a4 a5 confidentiality_def integrity_def attribute_constraints_def
              do_exec_def is_executable_def rule_exec_normal_def rule_exec_trusted_def
              pxn_policy_def uxn_policy_def
        by (smt (verit) Diff_cancel Operation.distinct(3) Operation.distinct(7)
            empty_iff fst_eqD insertE snd_eqD)
    next
      assume b0: "\<not> ((is_trusted_subject sub) \<and> (is_trusted_object ?t_objs obj))"
      then show ?thesis
        using a0 a1 a4 a5 b0 confidentiality_def integrity_def attribute_constraints_def
              do_exec_def is_executable_def rule_read_normal_def rule_exec_normal_def
              rule_exec_trusted_def pxn_policy_def uxn_policy_def
        by (smt (verit) Diff_cancel Operation.distinct(3) Operation.distinct(7)
            empty_iff fst_eqD insertE snd_eqD)
    qed
  }
  then show ?thesis
    by blast
qed

lemma do_exec_isolation_r :
  "prop_isolation_r (sub, obj, Exec, t_objs)"
  using prop_isolation_r_def transition_def do_exec_isolation
  by (metis (mono_tags, lifting) Operation.simps(16) old.prod.case)

lemma ta_enter_isolation :
  "\<forall> s s' b buf shadow_buf ca ta.
    (s', shadow_buf) = ta_enter s ca buf ta \<and>
    b \<in> (reqs s') - (reqs s) \<longrightarrow>
    (confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
proof -
  {
    fix s s' b buf shadow_buf ca ta
    assume a0: "(s', shadow_buf) = ta_enter s ca buf ta"
    assume a1: "b \<in> (reqs s') - (reqs s)"

    let ?objs = "objects s"
    let ?t_objs = "trusted_objs s"
    let ?priv = "min_priv_lst [(f2 buf), (f1 ca), (f1 ta)]"
    let ?new_id = "obj_id_generator s"
    let ?shadow_buf = "buf\<lparr> id := (the ?new_id), security_level := (?priv, Sec),
                            pxn := True, uxn := True \<rparr>"
    let ?new_objs = "?objs((the ?new_id) := Some ?shadow_buf)"
    let ?new_t_objs = "?t_objs \<union> {buf, ?shadow_buf}"
    let ?s1 = "s\<lparr> objects := ?new_objs, trusted_objs := ?new_t_objs \<rparr>"
    let ?req2 = "(trusted_sub, buf, Read, ?new_t_objs)"
    let ?rst2  = "do_read ?s1 trusted_sub buf"
    let ?s2 = "fst ?rst2"
    let ?d2 = "snd ?rst2"
    let ?req3 = "(trusted_sub, ?shadow_buf, Write, ?new_t_objs)"
    let ?rst3  = "do_write ?s2 trusted_sub ?shadow_buf"
    let ?s3 = "fst ?rst3"
    let ?d3 = "snd ?rst3"
    let ?objs2 = "objects ?s3"
    let ?t_objs2 = "trusted_objs ?s3"
    let ?new_objs2 = "?objs2((the ?new_id) := None)"
    let ?new_t_objs2 = "?t_objs2 - {buf, ?shadow_buf}"
    let ?s4 = "?s3\<lparr> trusted_objs := ?new_t_objs2 \<rparr>"

    have "(confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
    proof(cases "s' = s")
      assume b0: "s' = s"
      show ?thesis
        using a0 a1 b0 by auto
    next
      assume b0: "s' \<noteq> s"
      have b1: "s' = ?s4"
        using a0 a1 fst_conv snd_conv unfolding ta_enter_def
        by (smt (verit, ccfv_SIG) State.fold_congs(4) b0 case_prod_beta)
      have b2: "?new_id \<noteq> None \<and> ?d2 = Yes \<and> ?d3 = Yes"
        using a0 b0 unfolding ta_enter_def
        by (smt (verit, best) case_prod_conv old.prod.inject prod.collapse)
      have b3: "(trusted_objs ?s1) = (trusted_objs ?s2)"
        using fst_conv do_read_persist
        by (smt (verit, best) surj_pair)
      have b4: "trusted_objs ?s1 = ?new_t_objs" by auto
      have b5: "trusted_objs ?s2 = ?new_t_objs"
        using b3 b4 by blast

      have b6: "(reqs ?s1) = (reqs s)" by auto
      have b7: "(reqs ?s2) - (reqs ?s1) \<subseteq> {?req2}"
        using b4 do_read_reqs fst_conv
        by (metis surj_pair)
      have b8: "(reqs ?s3) - (reqs ?s2) \<subseteq> {?req3}"
        using b5 do_write_reqs fst_conv
        by (metis surj_pair)
      have b9: "(reqs s') = (reqs ?s3)"
        using b1 by auto
      have b10: "(reqs s') - (reqs s) \<subseteq> {?req2, ?req3}"
        using b6 b7 b8 b9
        by blast
      have b11: "b \<in> {?req2, ?req3}"
        using a1 b10 by blast

      have c1: "(confidentiality ?s2 ?req2 \<and> integrity ?s2 ?req2 \<and> attribute_constraints ?s2 ?req2)"
        using b2 b4 do_read_req_sec
        by (metis prod.exhaust_sel)
      have c2: "(confidentiality ?s3 ?req3 \<and> integrity ?s3 ?req3 \<and> attribute_constraints ?s3 ?req3)"
        using b2 b5 do_write_req_sec
        by (metis prod.exhaust_sel)
      have c3: "(confidentiality s' ?req2 \<and> integrity s' ?req2 \<and> attribute_constraints s' ?req2)"
        using c1 confidentiality_def integrity_def attribute_constraints_def
        by blast
      have c4: "(confidentiality s' ?req3 \<and> integrity s' ?req3 \<and> attribute_constraints s' ?req3)"
        using c2 confidentiality_def integrity_def attribute_constraints_def
        by blast
      show ?thesis
        using c3 c4 b11 by auto
    qed
  }
  then show ?thesis
    by blast
qed

lemma ta_exit_isolation :
  "\<forall> s s' b buf shadow_buf.
    s' = ta_exit s buf shadow_buf \<and>
    b \<in> (reqs s') - (reqs s) \<longrightarrow>
    (confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
proof -
  {
    fix s s' b buf shadow_buf ca ta
    assume a0: "s' = ta_exit s buf shadow_buf"
    assume a1: "b \<in> (reqs s') - (reqs s)"

    let ?obj_id = "id shadow_buf"
    let ?objs = "objects s"
    let ?t_objs = "trusted_objs s"
    let ?new_objs = "?objs(?obj_id := Some shadow_buf)"
    let ?new_t_objs = "?t_objs \<union> {buf, shadow_buf}"
    let ?s1 = "s\<lparr> trusted_objs := ?new_t_objs \<rparr>"
    let ?req2 = "(trusted_sub, shadow_buf, Read, ?new_t_objs)"
    let ?rst2 = "do_read ?s1 trusted_sub shadow_buf"
    let ?s2 = "fst ?rst2"
    let ?d2 = "snd ?rst2"
    let ?req3 = "(trusted_sub, buf, Write, ?new_t_objs)"
    let ?rst3 = "do_write ?s2 trusted_sub buf"
    let ?s3 = "fst ?rst3"
    let ?d3 = "snd ?rst3"
    let ?objs2 = "objects ?s3"
    let ?t_objs2 = "trusted_objs ?s3"
    let ?new_objs2 = "?objs2(?obj_id := None)"
    let ?new_t_objs2 = "?t_objs2 - {buf, shadow_buf}"
    let ?s4 = "?s3\<lparr> objects := ?new_objs2, trusted_objs := ?new_t_objs2 \<rparr>"

    have b1: "s' = ?s4"
      using a0 ta_exit_def
      by (smt (verit) case_prod_beta State.fold_congs(3) State.fold_congs(4))
    have b2: "(trusted_objs ?s1) = (trusted_objs ?s2)"
      using fst_conv do_read_persist
      by (smt (verit, best) surj_pair)
    have b3: "trusted_objs ?s1 = ?new_t_objs" by auto
    have b4: "trusted_objs ?s2 = ?new_t_objs"
      using b2 b3 by blast
    have b5: "(reqs ?s1) = (reqs s)" by auto
    have b6: "(reqs ?s2) - (reqs ?s1) \<subseteq> {?req2}"
      using b3 do_read_reqs fst_conv
      by (metis surj_pair)
    have b7: "(reqs ?s3) - (reqs ?s2) \<subseteq> {?req3}"
      using b4 do_write_reqs fst_conv
      by (metis surj_pair)
    have b8: "(reqs s') = (reqs ?s3)"
      using b1 by auto
    have b9: "(reqs s') - (reqs s) \<subseteq> {?req2, ?req3}"
      using b5 b6 b7 b8
      by blast
    have b10: "b \<in> {?req2, ?req3}"
      using a1 b9 by blast

    have c1: "(reqs ?s2) - (reqs ?s1) \<noteq> {} \<longrightarrow>
              (confidentiality ?s2 ?req2 \<and> integrity ?s2 ?req2 \<and> attribute_constraints ?s2 ?req2)"
      using b3 do_read_req_not_empty_sec
      by (metis prod.exhaust_sel)
    have c2: "(reqs ?s3) - (reqs ?s2) \<noteq> {} \<longrightarrow>
              (confidentiality ?s3 ?req3 \<and> integrity ?s3 ?req3 \<and> attribute_constraints ?s3 ?req3)"
      using b4 do_write_req_not_empty_sec
      by (metis prod.exhaust_sel)
    have c3: "(confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
      using a1 b5 b6 b7 b8 c1 c2
            confidentiality_def integrity_def attribute_constraints_def
      by (smt (verit) Diff_iff Diff_partition insert_iff  singleton_Un_iff)
  }
  then show ?thesis
    by blast
qed

lemma ta_call_isolation :
  "\<forall> s s' b d ca buf ta.
    (s', d) = ta_call s ca buf ta \<longrightarrow>
    b \<in> (reqs s') - (reqs s) \<longrightarrow>
    (confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
proof -
  {
    fix s s' b d ca buf ta
    assume a0: "(s', d) = ta_call s ca buf ta"
    assume a1: "b \<in> (reqs s') - (reqs s)"
    have "(confidentiality s' b \<and> integrity s' b \<and> attribute_constraints s' b)"
    proof(cases "s' = s")
      assume b0: "s' = s"
      then show ?thesis
        using a1 by auto
    next
      assume b0: "s' \<noteq> s"
      let ?rst = "ta_enter s ca buf ta"
      let ?s1 = "fst ?rst"
      let ?shadow_buf = "snd ?rst"
      let ?s2 = "ta_exit ?s1 buf (the ?shadow_buf)"

      have b1: "?s2 = s'"
        using a0 b0 ta_call_def
        by (smt (verit) Pair_inject case_prod_unfold)
      have b2: "?shadow_buf \<noteq> None"
        using a0 b0 ta_call_def
        by (smt (verit, del_insts) Pair_inject split_beta)
      have b3: "?s1 \<noteq> s"
        using b2 ta_enter_helper2
        by (metis (no_types, opaque_lifting) surjective_pairing)
      have b4: "\<forall> r \<in> ((reqs ?s1) - (reqs s)).
               (confidentiality ?s1 r \<and> integrity ?s1 r \<and> attribute_constraints ?s1 r)"
        using b2 b3 ta_enter_isolation
        by (metis prod.exhaust_sel)
      have b5: "\<forall> r \<in> ((reqs ?s1) - (reqs s)).
               (confidentiality s' r \<and> integrity s' r \<and> attribute_constraints s' r)"
        using b4 confidentiality_def integrity_def attribute_constraints_def
        by blast
      have b6: "\<forall> r \<in> ((reqs s') - (reqs ?s1)).
               (confidentiality s' r \<and> integrity s' r \<and> attribute_constraints s' r)"
        using b1 ta_exit_isolation
        by blast
      have b7: "b \<in> ((reqs ?s1) - (reqs s)) \<union> ((reqs s') - (reqs ?s1))"
        using a0 a1 b0 b1
        by blast
      show ?thesis using b5 b6 b7
        by blast
    qed
  }
  then show ?thesis
    by blast
qed

lemma ta_call_isolation_r :
  "prop_isolation_r (sub, obj, TA_Call ta, t_objs)"
  using prop_isolation_r_def transition_def ta_call_isolation
  by (metis (mono_tags, lifting) Operation.simps(17) old.prod.case)

subsection \<open> Operations satisfy noninterference \<close>

lemma do_read_nonintf :
  "\<forall> s s' d sub obj.
    (s', d) = do_read s sub obj \<longrightarrow>
    (\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
    (\<forall> j. equiv_obj_attr ((objects s) j) ((objects s') j))"
  using do_read_def equiv_sub_attr_def equiv_obj_attr_def
  by (smt (verit) Pair_inject State.select_convs(2) State.select_convs(3)
      State.surjective State.update_convs(1))

lemma do_read_nonintf_r :
  "noninterference_r (sub, obj, Read, t_objs)"
  using noninterference_r_def transition_def do_read_nonintf
  by fastforce

lemma do_write_nonintf :
  "\<forall> s s' d sub obj.
    (s', d) = do_write s sub obj \<longrightarrow>
    (\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
    (\<forall> j. equiv_obj_attr ((objects s) j) ((objects s') j))"
  using do_write_def equiv_sub_attr_def equiv_obj_attr_def
  by (smt (verit) Pair_inject State.select_convs(2) State.select_convs(3)
      State.surjective State.update_convs(1))

lemma do_write_nonintf_r :
  "noninterference_r (sub, obj, Write, t_objs)"
  using noninterference_r_def transition_def do_write_nonintf
  by fastforce

lemma do_exec_nonintf :
  "\<forall> s s' d sub obj.
    (s', d) = do_exec s sub obj \<longrightarrow>
    (\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
    (\<forall> j. equiv_obj_attr ((objects s) j) ((objects s') j))"
  using do_exec_def equiv_sub_attr_def equiv_obj_attr_def
  by (smt (verit) Pair_inject State.select_convs(2) State.select_convs(3)
      State.surjective State.update_convs(1))

lemma do_exec_nonintf_r :
  "noninterference_r (sub, obj, Exec, t_objs)"
  using noninterference_r_def transition_def do_exec_nonintf
  by fastforce

lemma ta_enter_nonintf :
  "\<forall> s s' buf shadow_buf ca ta.
    (s', shadow_buf) = ta_enter s ca buf ta \<longrightarrow>
    (s' = s) \<or>
    (s' \<noteq> s \<and>
     idc_policy buf (the shadow_buf) \<and>
     (\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
     (\<forall> j \<noteq> (id (the shadow_buf)). equiv_obj_attr ((objects s) j) ((objects s') j)))"
proof -
  {
    fix s s' buf shadow_buf ca ta
    assume a0: "(s', shadow_buf) = ta_enter s ca buf ta"
    assume a1: "s' \<noteq> s"

    let ?objs = "objects s"
    let ?t_objs = "trusted_objs s"
    let ?priv = "min_priv_lst [(f2 buf), (f1 ca), (f1 ta)]"
    let ?new_id = "obj_id_generator s"
    let ?shadow_buf = "buf\<lparr> id := (the ?new_id), security_level := (?priv, Sec),
                            pxn := True, uxn := True \<rparr>"
    let ?new_objs = "?objs((the ?new_id) := Some ?shadow_buf)"
    let ?new_t_objs = "?t_objs \<union> {buf, ?shadow_buf}"
    let ?s1 = "s\<lparr> objects := ?new_objs, trusted_objs := ?new_t_objs \<rparr>"
    let ?rst2  = "do_read ?s1 trusted_sub buf"
    let ?s2 = "fst ?rst2"
    let ?d2 = "snd ?rst2"
    let ?rst3  = "do_write ?s2 trusted_sub ?shadow_buf"
    let ?s3 = "fst ?rst3"
    let ?d3 = "snd ?rst3"
    let ?objs2 = "objects ?s3"
    let ?t_objs2 = "trusted_objs ?s3"
    let ?new_objs2 = "?objs2((the ?new_id) := None)"
    let ?new_t_objs2 = "?t_objs2 - {buf, ?shadow_buf}"
    let ?s4 = "?s3\<lparr> trusted_objs := ?new_t_objs2 \<rparr>"

    have a2: "shadow_buf \<noteq> None"
      using a0 a1 ta_enter_helper by metis

    have b1: "s' = ?s4"
      using a0 a1 fst_conv snd_conv unfolding ta_enter_def
      by (smt (verit) State.fold_congs(3) State.fold_congs(4) case_prod_conv prod.collapse)
    have b2: "(the shadow_buf) = ?shadow_buf"
      using a0 a2 fst_conv snd_conv unfolding ta_enter_def
      by (smt (verit) case_prod_beta option.collapse option.inject)

    have b3: "(subjects ?s1) = (subjects ?s2) \<and>
              (objects ?s1) = (objects ?s2) \<and>
              (trusted_objs ?s1) = (trusted_objs ?s2)"
      using fst_conv do_read_persist
      by (smt (verit, best) surj_pair) 
    have b4: "(subjects ?s3) = (subjects ?s2) \<and>
              (objects ?s3) = (objects ?s2) \<and>
              (trusted_objs ?s3) = (trusted_objs ?s2)"
      using fst_conv do_write_persist
      by (smt (verit, best) surj_pair)

    have b5: "(subjects s) = (subjects s')"
      using b1 b3 b4 by simp

    have b6: "?new_id \<noteq> None"
      using a0 a1 Pair_inject unfolding ta_enter_def
      by fastforce
    have b7: "((objects s) (the ?new_id)) = None"
      using b6 obj_id_generator_def
      by (metis (mono_tags, lifting) exE_some option.sel)
    have b8: "((objects s) (id (the shadow_buf))) = None"
      using b2 b7 by auto
    have b9: "\<forall> j. (objects s) j \<noteq> None \<longrightarrow> j \<noteq> (id (the shadow_buf))"
      using b2 b7 by auto

    have b10: "\<forall> j \<noteq> (id (the shadow_buf)). equiv_obj_attr ((objects s) j) ((objects ?s1) j)"
      using b2 b9 equiv_obj_attr_def
      by simp
    have b11: "\<forall> j \<noteq> (id (the shadow_buf)). equiv_obj_attr ((objects s) j) ((objects ?s3) j)"
      using b3 b4 b10
      by simp
    have b12: "\<forall> j \<noteq> (id (the shadow_buf)). equiv_obj_attr ((objects s) j) ((objects ?s4) j)"
      using b2 b9 b11 equiv_obj_attr_def
      by simp

    have c1: "idc_policy buf (the shadow_buf)"
      using b2 idc_policy_def is_attr_ge_def
      by simp
    have c2: "\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)"
      using b5 equiv_sub_attr_def
      by simp
    have c3: "\<forall> j \<noteq> (id (the shadow_buf)). equiv_obj_attr ((objects s) j) ((objects s') j)"
      using b1 b12 
      by blast
    have "idc_policy buf (the shadow_buf) \<and>
          (\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
          (\<forall> j \<noteq> (id (the shadow_buf)). equiv_obj_attr ((objects s) j) ((objects s') j))"
      using c1 c2 c3
      by simp
  }
  then show ?thesis
    by blast
qed

lemma ta_exit_nonintf :
  "\<forall> s s' buf shadow_buf.
    s' = ta_exit s buf shadow_buf \<longrightarrow>
    (\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
    (\<forall> j \<noteq> (id shadow_buf). equiv_obj_attr ((objects s) j) ((objects s') j)) \<and>
    ((objects s') (id shadow_buf)) = None"
proof -
  {
    fix s s' buf shadow_buf
    assume a0: "s' = ta_exit s buf shadow_buf"

    let ?obj_id = "id shadow_buf"
    let ?objs = "objects s"
    let ?t_objs = "trusted_objs s"
    let ?new_objs = "?objs(?obj_id := Some shadow_buf)"
    let ?new_t_objs = "?t_objs \<union> {buf, shadow_buf}"
    let ?s1 = "s\<lparr> trusted_objs := ?new_t_objs \<rparr>"
    let ?rst2 = "do_read ?s1 trusted_sub shadow_buf"
    let ?s2 = "fst ?rst2"
    let ?d2 = "snd ?rst2"
    let ?rst3 = "do_write ?s2 trusted_sub buf"
    let ?s3 = "fst ?rst3"
    let ?d3 = "snd ?rst3"
    let ?objs2 = "objects ?s3"
    let ?t_objs2 = "trusted_objs ?s3"
    let ?new_objs2 = "?objs2(?obj_id := None)"
    let ?new_t_objs2 = "?t_objs2 - {buf, shadow_buf}"
    let ?s4 = "?s3\<lparr> objects := ?new_objs2, trusted_objs := ?new_t_objs2 \<rparr>"

    have b1: "s' = ?s4"
      using a0 ta_exit_def
      by (smt (verit) case_prod_beta State.fold_congs(3) State.fold_congs(4))
    have b2: "(subjects ?s1) = (subjects ?s2) \<and>
              (objects ?s1) = (objects ?s2) \<and>
              (trusted_objs ?s1) = (trusted_objs ?s2)"
      using fst_conv do_read_persist
      by (smt (verit, best) surj_pair)
    have b3: "(subjects ?s3) = (subjects ?s2) \<and>
              (objects ?s3) = (objects ?s2) \<and>
              (trusted_objs ?s3) = (trusted_objs ?s2)"
      using fst_conv do_write_persist
      by (smt (verit, best) surj_pair)
    have b4: "(subjects s) = (subjects s')"
      using b1 b2 b3 by simp
    have b5: "\<forall> j \<noteq> (id shadow_buf). equiv_obj_attr ((objects s) j) ((objects ?s1) j)"
      using equiv_obj_attr_def
      by simp
    have b6: "\<forall> j \<noteq> (id shadow_buf). equiv_obj_attr ((objects s) j) ((objects ?s3) j)"
      using b2 b3 b5
      by simp
    have b7: "\<forall> j \<noteq> (id shadow_buf). equiv_obj_attr ((objects s) j) ((objects ?s4) j)"
      using b6 equiv_obj_attr_def
      by simp

    have c1: "\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)"
      using b4 equiv_sub_attr_def
      by simp
    have c2: "\<forall> j \<noteq> (id shadow_buf). equiv_obj_attr ((objects s) j) ((objects s') j)"
      using b1 b7
      by blast
    have c3: "(objects s') (id shadow_buf) = None"
      using b1 by simp
    have "(\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
          (\<forall> j \<noteq> (id shadow_buf). equiv_obj_attr ((objects s) j) ((objects s') j)) \<and>
          ((objects s') (id shadow_buf)) = None"
      using c1 c2 c3
      by simp
  }
  then show ?thesis
    by simp
qed

lemma ta_call_nonintf :
  "\<forall> s s' d ca buf ta.
    (s', d) = ta_call s ca buf ta \<longrightarrow>
    (\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
    (\<forall> j. equiv_obj_attr ((objects s) j) ((objects s') j))"
proof -
  {
    fix s s' d ca buf ta
    assume a0: "(s', d) = ta_call s ca buf ta"
    have "(\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
          (\<forall> j. equiv_obj_attr ((objects s) j) ((objects s') j))"
    proof(cases "s' = s")
      assume b0: "s' = s"
      then show ?thesis
        using equiv_sub_attr_def equiv_obj_attr_def
        by simp
    next
      assume b0: "s' \<noteq> s"
      let ?rst = "ta_enter s ca buf ta"
      let ?s1 = "fst ?rst"
      let ?shadow_buf = "snd ?rst"
      let ?s2 = "ta_exit ?s1 buf (the ?shadow_buf)"

      have b1: "?s2 = s'"
        using a0 b0 ta_call_def
        by (smt (verit) Pair_inject case_prod_unfold)
      have b2: "?shadow_buf \<noteq> None"
        using a0 b0 ta_call_def
        by (smt (verit, del_insts) Pair_inject split_beta)
      have b3: "?s1 \<noteq> s"
        using b2 ta_enter_helper2
        by (metis (no_types, opaque_lifting) surjective_pairing)

      have b4: "(\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects ?s1) i)) \<and>
                (\<forall> j \<noteq> (id (the ?shadow_buf)). equiv_obj_attr ((objects s) j) ((objects ?s1) j))"
        using b2 b3 ta_enter_nonintf
        by (metis prod.exhaust_sel)
      have b5: "(\<forall> i. equiv_sub_attr ((subjects ?s1) i) ((subjects ?s2) i)) \<and>
                (\<forall> j \<noteq> (id (the ?shadow_buf)). equiv_obj_attr ((objects ?s1) j) ((objects ?s2) j))"
        using ta_exit_nonintf
        by simp
      have b6: "(\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects ?s2) i)) \<and>
                (\<forall> j \<noteq> (id (the ?shadow_buf)). equiv_obj_attr ((objects s) j) ((objects ?s2) j))"
        using b4 b5 equiv_sub_attr_def equiv_obj_attr_def
              equiv_sub_attr_transitive equiv_obj_attr_transitive
        by fast

      let ?objs = "objects s"
      let ?t_objs = "trusted_objs s"
      let ?priv = "min_priv_lst [(f2 buf), (f1 ca), (f1 ta)]"
      let ?new_id = "obj_id_generator s"

      have b7: "?new_id \<noteq> None"
        using b3 fst_conv unfolding ta_enter_def
        by fastforce 
      have b8: "(the ?shadow_buf) = buf\<lparr>
                    id := (the ?new_id), security_level := (?priv, Sec),
                    pxn := True, uxn := True \<rparr>"
        using b2 snd_conv unfolding ta_enter_def
        by (smt (verit, del_insts) option.sel split_beta)

      have b9: "((objects s) (the ?new_id)) = None"
        using b7 obj_id_generator_def
        by (metis (mono_tags, lifting) exE_some option.sel)
      have b10: "((objects s) (id (the ?shadow_buf))) = None"
        using b8 b9 by auto
      have b11: "((objects ?s2) (id (the ?shadow_buf))) = None"
        using ta_exit_nonintf by simp
      have b12: "((objects s') (id (the ?shadow_buf))) = None"
        using b1 b11 by blast

      have c1: "(\<forall> i. equiv_sub_attr ((subjects s) i) ((subjects s') i)) \<and>
                (\<forall> j \<noteq> (id (the ?shadow_buf)). equiv_obj_attr ((objects s) j) ((objects s') j))"
        using b1 b6 by simp

      show ?thesis using c1 b10 b12 equiv_obj_attr_def
        by (smt (verit, ccfv_threshold))
    qed
  }
  then show ?thesis
    by simp
qed

lemma ta_call_nonintf_r :
  "noninterference_r (sub, obj, TA_Call ta, t_objs)"
  using noninterference_r_def transition_def ta_call_nonintf
  by fastforce


subsection \<open> Transition Security \<close>

theorem prop_isolation_sat : prop_isolation
proof -
  {
    fix r
    have "prop_isolation_r r"
      apply(induct r)
      using do_read_isolation_r do_write_isolation_r do_exec_isolation_r ta_call_isolation_r
      by (metis Operation.exhaust)
  }
  then show ?thesis
    using prop_isolation_def prop_isolation_r_def
    by blast
qed

theorem noninterference_sat : noninterference
proof -
  {
    fix r
    have "noninterference_r r"
      apply(induct r)
      using do_read_nonintf_r do_write_nonintf_r do_exec_nonintf_r ta_call_nonintf_r
      by (metis Operation.exhaust)
  }
  then show ?thesis
    using noninterference_def noninterference_r_def
    by simp
qed

end