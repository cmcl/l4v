text\<open>Top-level system call interface for SMOS\<close>
theory Syscall_S
imports Structures_S "Lib.NonDetMonad"
begin

text\<open>Find proc entry corresponding to pid\<close>
definition find_proc_entry :: "PID \<Rightarrow> proc smos_monad" where
"find_proc_entry i \<equiv> do
  procs \<leftarrow> gets procs;
  assert_opt (fst procs i)
od"

definition extend :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b option)" where
"extend f i p \<equiv> \<lambda>j. if j = i then Some p else f j"

definition upd_proc :: "PID \<Rightarrow> proc \<Rightarrow> unit smos_monad" where
"upd_proc i p \<equiv> do
   ps \<leftarrow> gets procs;
   modify (\<lambda>s. s\<lparr> procs := (\<lambda>j. if i = j then Some p else fst ps j, snd ps) \<rparr>)
od"

definition upd_handles :: "handle \<Rightarrow> resource \<Rightarrow> proc \<Rightarrow> unit smos_monad" where
"upd_handles h r p \<equiv>
   let (rs, h) = p_handles p in
   upd_proc (p_id p) (p\<lparr> p_handles := (extend rs h r, h)\<rparr>)"

text\<open>Window allocation\<close>
definition upd_window :: "nat \<Rightarrow> window \<Rightarrow> unit smos_monad" where
"upd_window i w \<equiv>
   modify (\<lambda>s. s\<lparr> windows := (\<lambda>j. if i = j then Some w else fst (windows s) j, snd (windows s))\<rparr>)"

definition free_window_index :: "nat smos_monad" where
"free_window_index \<equiv> do
  (ws, c) \<leftarrow> gets windows;
  modify (\<lambda>s. s\<lparr> windows := (ws, c + 1)\<rparr>);
  return c
od"

text\<open>Find a free slot for a server. Our model diverges slightly from the real code which has a fixed
size collection of servers.\<close>

definition free_server_index :: "nat smos_monad" where
"free_server_index \<equiv> do
   (xs, c) \<leftarrow> gets servers;
   modify (\<lambda>s. s\<lparr> servers := (xs, c + 1)\<rparr>);
   return c
od"

definition new_window :: "nat \<Rightarrow> nat \<Rightarrow> PID \<Rightarrow> SecCtxt \<Rightarrow> window" where
"new_window b sz i sc \<equiv> \<lparr> w_base = b, w_size = sz, w_rsm = False, w_pid = i, w_sc = sc \<rparr>" 

text\<open>Specification of handle allocation\<close>
definition free_handle :: "PID \<Rightarrow> handle smos_monad" where
"free_handle i \<equiv> do
   p \<leftarrow> find_proc_entry i;
   let (rs, h) = p_handles p in
      do ps \<leftarrow> gets procs;
         upd_proc i (p\<lparr> p_handles := (rs, h + 1) \<rparr>);
         return h
      od
od"

text\<open>Security service authorisation procedure\<close>

fun smos_authorise :: "SecCtxt \<Rightarrow> SecCtxt \<Rightarrow> op_desc \<Rightarrow> bool smos_monad" where
"smos_authorise subj obj _ = return (subj \<le> obj)"

text\<open>A server is authorised to publish if its name is contained within the set of authorised
servers.\<close>

definition smos_conn_publish_authorise :: "name \<Rightarrow> proc \<Rightarrow> bool smos_monad" where
"smos_conn_publish_authorise n p \<equiv> do
  allowed_srvs \<leftarrow> gets auth_servers;
  return (n \<in> allowed_srvs)
od"

text\<open>Specification of creating a process\<close>
definition new_proc :: "PID \<Rightarrow> SecCtxt \<Rightarrow> obj_ref \<Rightarrow> proc" where
"new_proc i sc r = \<lparr> p_id = i , p_sc = sc , p_cspace = (\<lambda>_.None, 0) , p_handles = (\<lambda>_.None, 0) , p_ref = r \<rparr>"

definition proc_create_impl :: "SecCtxt \<Rightarrow> PID smos_monad" where
"proc_create_impl sc \<equiv> do
   (ps, i) \<leftarrow> gets procs;
   r \<leftarrow> alloc_ko (Thread (TProc i));
   modify (\<lambda>s. s\<lparr> procs := (extend ps i (new_proc i sc r), i + 1) \<rparr>);
   return i
od"

definition smos_proc_create :: "SecCtxt \<Rightarrow> (PID \<times> handle) smos_monad" where
"smos_proc_create sc \<equiv> do
   pid \<leftarrow> gets calling_pid;
   subject \<leftarrow> find_proc_entry pid;
   is_authorised \<leftarrow> smos_authorise (p_sc subject) sc ProcCreateOp;
   if \<not>is_authorised then fail
   else do
      i \<leftarrow> proc_create_impl sc;
      return (i, 0)
   od
od"

text\<open>Specification of creating a window\<close>
definition smos_window_create_impl :: "PID \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> handle smos_monad" where
"smos_window_create_impl i base win_size \<equiv> do
   p \<leftarrow> find_proc_entry i;
   h \<leftarrow> free_handle i;
   w \<leftarrow> free_window_index;
   upd_window w (new_window base win_size i (p_sc p));
   upd_handles h (Window w) p;
   return h
od"

definition smos_window_create :: "nat \<Rightarrow> nat \<Rightarrow> handle smos_monad" where
"smos_window_create base win_size \<equiv> do
   pid \<leftarrow> gets calling_pid;
   subject \<leftarrow> find_proc_entry pid;
   is_authorised \<leftarrow> smos_authorise (p_sc subject) (p_sc subject) WindowCreateOp;
   if \<not>is_authorised then fail
   else do
     hdl \<leftarrow> smos_window_create_impl pid base win_size;
     return hdl
   od
od"

text\<open>Specification of a process publishing as a server\<close>

definition smos_conn_publish :: "cslot \<Rightarrow> name \<Rightarrow> handle smos_monad" where
"smos_conn_publish k n \<equiv> return 0"

fun do_operation :: "operation \<Rightarrow> unit smos_monad" where
"do_operation (ProcCreate sc) = do (i,h) \<leftarrow> smos_proc_create sc; return () od" |
"do_operation (WindowCreate wb wsz) = do h \<leftarrow> smos_window_create wb wsz; return () od" |
"do_operation (ConnPublish k n) = return ()" |
"do_operation (ObjCreate k attr sz sc) = return ()"

fun do_user_op :: "event \<Rightarrow> unit smos_monad" where
"do_user_op (Syscall i op) = do () \<leftarrow> modify (set_calling_pid i); do_operation op od"

abbreviation before :: "event \<Rightarrow> state \<Rightarrow> bool" where
"before e s \<equiv> invs s \<and> admissible s e \<and> authorised s e"

end