theory Syscall_SI
imports "SSpec.Syscall_S" "Lib.NonDetMonadLemmaBucket"
begin

lemma smos_authorise_wp[wp]:
  "\<lbrace> \<lambda>s. P (subj \<le> obj) s \<rbrace> smos_authorise subj obj op \<lbrace> P \<rbrace>"
  apply simp
  by wp

lemma find_proc_entry_wp[wp]:
  "\<lbrace> \<lambda>s. P (the (fst (procs s) i)) s \<rbrace> find_proc_entry i \<lbrace> P \<rbrace>"
  unfolding find_proc_entry_def
  by (wpsimp)

lemma alloc_ko_wp[wp]:
  "\<lbrace> \<lambda>s. P (snd (kheap s)) (s\<lparr> kheap := (extend (fst (kheap s)) (snd (kheap s)) ko, snd (kheap s) +1)\<rparr>)  \<rbrace>
    alloc_ko ko
   \<lbrace> P \<rbrace>"
  unfolding alloc_ko_def extend_def
  by wpsimp

text\<open>Creating a process is valid and preserves the system state invariants. We require the creating
process to exist and its security context to dominate the security context of the spawned process.\<close>

lemma smos_proc_create_valid:
  "\<lbrace> before (Syscall i (ProcCreate sc)) \<rbrace> smos_proc_create sc \<lbrace> \<lambda>x. invs \<rbrace>"
  unfolding smos_proc_create_def proc_create_impl_def
  apply wpsimp
  by (auto simp add: invs_def pid_bound_def valid_pid_def extend_def valid_servers_def
                     enforces_policy_def must_dominate_def subjects_def)
  

lemma smos_window_create_valid:
  "\<lbrace> before (Syscall i (WindowCreate base sz)) \<rbrace> smos_window_create base sz \<lbrace> \<lambda>s. invs \<rbrace>"
  unfolding smos_window_create_def smos_window_create_impl_def upd_window_def
            upd_handles_def upd_proc_def free_window_index_def
            free_handle_def
  apply wpsimp
  by (auto simp add: invs_def pid_bound_def valid_pid_def extend_def valid_servers_def
                     enforces_policy_def must_dominate_def subjects_def)

text\<open>The main theorem states all possible SMOS API calls are valid and preserve the invariants
provided the event and system state before the call satisfies the `before` predicate.\<close>
lemma all_events_valid:
  "\<lbrace> before e \<rbrace>
   do_user_op e
   \<lbrace> \<lambda>x. invs \<rbrace>"
   sorry
   
end      