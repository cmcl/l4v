text\<open>The main SMOS data types and type definitions in the abstract model.\<close>
theory Structures_S
imports "Lib.NonDetMonad"
begin

text\<open>A handle is a connection-visible identifier for a SMOS object.\<close>
type_synonym handle = nat

abbreviation INVALID_HDL :: "handle" where
"INVALID_HDL \<equiv> 0"

text\<open>A handle cap is a transferable token that identifies a SMOS object but can only refer to
the object within the context of the implementing server. A bit more general than mere handles.\<close>
type_synonym handle_cap = nat

text\<open>Each process is associated with a unique process identifier. These process identifiers can be
reused.\<close>
type_synonym PID = nat

text\<open>A security context is just a wrapper over a handle. \<close>
type_synonym SecCtxt = handle

text\<open>Userland servers publish under a name which for simplicity we represent as a number.\<close>
type_synonym name = nat

text\<open>A handle reference contains a resource which indexes into the system state.\<close>
datatype resource = Window nat | Object nat | View | Connection | NoResource

text\<open>Some basic access rights for objects within SMOS.\<close>
datatype rights = Read | Write | Exec | Send | Recv

text\<open>A simplified model for threads in the system. An executing thread corresponds either to a
SMOS process, or the SMOS server. This abstraction approximates seL4 TCBs for the corresponding
object at the SMOS level.\<close>
datatype thread = TProc PID | TSMOS

text\<open>Basic modelling of the underlying seL4 objects that are crucial to the communication
architecture\<close>

text\<open>A kernel object identifier\<close>
type_synonym obj_ref = nat

text\<open>An entry in the capability space\<close>
type_synonym cslot = nat

text\<open>Abstraction over seL4 badge mechanism for identifying clients involved in IPC\<close>
type_synonym badge = nat

text\<open>The capabilities we consider in our model. The definition of an endpoint is borrowed from L4v,
basically encoding a blocking semantics. Threads be either blocked on sending, or receiving.\<close>

datatype endpoint = IdleEP
                  | SendEP "obj_ref list"
                  | RecvEP "obj_ref list"

datatype cap = EndpointCap obj_ref "rights set" "badge option"

text\<open>A kernel object is an abstraction of the objects provided by seL4. In particular, we only model
endpoints and our representation of TCBs (i.e. threads) is simplified to return the SMOS relevant
component.\<close>

datatype kernel_object = Endpoint endpoint
                       | Thread thread

text\<open>A generic type for representing table data. Resources in SMOS are allocated from fixed size
arrays which can be represented functionally using a mapping from an index to objects paired with
the next index to allocate.\<close>
type_synonym 'a table = "(nat \<Rightarrow> 'a option) \<times> nat"

text\<open>Process state modelled after SMOS struct sm_proc. This structure abstracts from the
implementation details of an underlying process and concerns itself with only identifiers
and security relevant fields:

p_cspace is an abstraction of the cspace of the process, mapping slots to capabilities.

p_handles is the handle table for the process, mapping handles to resources allocated to this
process.\<close>

record proc =
  p_id :: PID
  p_sc :: SecCtxt
  p_cspace :: "cap table"
  p_handles :: "resource table"
  p_ref :: obj_ref (* corresponds to its TCB at the seL4 level *)

text\<open>A window object is a virtual address space range of a particular process. A window is uniquely
     identified by its handle within a process.\<close>

record window =
  w_base :: nat
  w_size :: nat
  w_rsm :: bool (* Flag is true if window is managed by resource server *)
  w_pid :: PID
  w_sc :: SecCtxt (* Inherited from creating process *)

text\<open>An object is an abstraction of server-implemented state which may be accessible to clients
through windows mapped by servers. One example of an object is that of a file provided by a file
server mapped into a client's address space using anonymous memory object and a window. Objects are
identified by their handles.\<close>

datatype object_attributes = MEM_ANON | MEM_CPIO

record object =
  obj_sec_ctxt :: handle
  obj_size :: nat
  obj_attr :: object_attributes
  obj_sc   :: SecCtxt
  obj_ws   :: "nat table" (* windows *)

text\<open>A published process becomes a server with some extra bookkeeping to track its published name
and communication architecture\<close>
record server =
  s_pid :: PID
  s_name :: nat (* names are just numbers for simplicity *)
  s_ep :: cap (* Server endpoint to recv on *)

text\<open>A connection provides access to a server via an seL4 endpoint capability.\<close>
record connection =
  conn_from :: PID
  conn_to   :: server
  conn_ep   :: cap (* badged endpoint to server *)
  conn_reg  :: handle (* server registration handle *)

text\<open>The system state keeps track of processes, their security context and other resources. The
state also encapsulates the behaviour of the root task, i.e. SMOS server.\<close>

record state =
  windows :: "window table"
  objects :: "object table"
  procs :: "proc table"
  servers :: "server table"
  conns :: "connection table"
  auth_servers :: "name set"
  kheap :: "kernel_object table"
  cspace :: "cap table"
  smos_server :: obj_ref (* TCB object for SMOS server *)
  calling_pid :: PID

text\<open>SMOS API operations correspond to API functions and an event is a particular
     instance generated by client processes.\<close>
datatype op_desc = ProcCreateOp | WindowCreateOp | ObjCreateOp | ConnPublishOp

datatype operation = ProcCreate SecCtxt
                   | WindowCreate nat nat
                   | ObjCreate cslot object_attributes nat SecCtxt
                   | ConnPublish cslot name

text\<open>Events represent interactions between processes within the SMOS system. The main interaction is
a Syscall which is an invocation of a SMOS API function by a client (SMOS) process. In reality this
happens via seL4 IPC mechanisms which we abstract away in this model. Another possible interaction
is between two SMOS processes where one acts as a server.\<close>

datatype event = Syscall PID operation

text\<open>L4.verified monad specialised to SMOS system state\<close>

type_synonym 'a smos_monad = "(state, 'a) nondet_monad"

text\<open>Operations on the SMOS system state\<close>

text\<open>Generic operations on tables\<close>

text\<open>Operations on the kheap. This part of the system state is an abstraction of allocated seL4
objects. It does not model all seL4 kernel objects / resources but only those used by the live SMOS
objects in the system. For that reason, kheap allocation looks "dynamic" but simply corresponds to
allocating untypeds + retyping.\<close>

definition alloc_ko :: "kernel_object \<Rightarrow> obj_ref smos_monad" where
"alloc_ko ko \<equiv> do
   kh \<leftarrow> gets kheap;
   let ref = snd kh in do
     modify (\<lambda>s. s\<lparr> kheap := (\<lambda>r. if r = ref then Some ko else fst kh r, ref + 1) \<rparr>);
     return ref
   od
od"

definition alloc_cap :: "cap \<Rightarrow> cslot smos_monad" where
"alloc_cap c \<equiv> do
   cs \<leftarrow> gets cspace;
   let k = snd cs in do
     modify (\<lambda>s. s\<lparr> cspace := (\<lambda>j. if j = k then Some c else fst cs j, k + 1) \<rparr>);
     return k
   od
od"

fun get_proc :: "state \<Rightarrow> PID \<Rightarrow> proc option" where
"get_proc s i = fst (procs s) i"

fun get_server :: "state \<Rightarrow> name \<Rightarrow> server option" where
"get_server s n = fst (servers s) n"

fun next_pid :: "state \<Rightarrow> PID" where
"next_pid s = snd (procs s)"

fun get_sec_ctxt :: "state \<Rightarrow> PID \<Rightarrow> SecCtxt" where
"get_sec_ctxt s i = (case get_proc s i of
    None \<Rightarrow> 0
  | Some p \<Rightarrow> p_sc p)"

fun is_send_endpoint :: "cap \<Rightarrow> bool" where
"is_send_endpoint (EndpointCap _ rs _) = (Send \<in> rs)"

definition valid_pid :: "PID \<Rightarrow> state \<Rightarrow> bool" where
"valid_pid i s \<equiv> \<exists>p. get_proc s i = Some p \<and> p_id p = i"

definition dominates :: "SecCtxt \<Rightarrow> SecCtxt \<Rightarrow> bool" where
"dominates x y \<equiv> x \<le> y"

definition set_calling_pid :: "PID \<Rightarrow> state \<Rightarrow> state" where
"set_calling_pid i s \<equiv> s\<lparr> calling_pid := i \<rparr>"

definition free_cslot :: "state \<Rightarrow> PID \<Rightarrow> cslot \<Rightarrow> bool" where
"free_cslot s i k \<equiv> \<exists>p. get_proc s i = Some p \<and> fst (p_cspace p) k = None"

definition valid_server_endpoint :: "state \<Rightarrow> PID \<Rightarrow> cslot \<Rightarrow> bool" where
"valid_server_endpoint s i ep \<equiv>
   \<exists>p c. get_proc s i = Some p \<and> fst (p_cspace p) ep = Some c \<and> is_send_endpoint c"

text\<open>Invariants on the SMOS system state\<close>

definition pid_bound :: "state \<Rightarrow> bool" where
"pid_bound s \<equiv> \<forall>i. valid_pid i s \<longrightarrow> i < next_pid s"

abbreviation valid_caller :: "state \<Rightarrow> bool" where
"valid_caller s \<equiv> valid_pid (calling_pid s) s"

definition valid_servers :: "state \<Rightarrow> bool" where
"valid_servers s \<equiv> \<forall>n.\<exists>srv. get_server s n = Some srv \<longrightarrow> s_name srv \<in> auth_servers s"

text\<open>All subjects within the system must satisfy a simple security policy: their security context
must dominate all objects to which they have access. Our security model is explicit
for now but will be revised to a parameter later.\<close>

text\<open>Subjects are defined as all the active processes within the system.\<close>

definition subjects :: "state \<Rightarrow> proc set" where
"subjects s \<equiv> {p | p. \<forall>i. i < snd (procs s) \<and> (fst (procs s) i = Some p) }"

text\<open>Obtain the set of all resources accessible by a process\<close>
definition resources :: "proc \<Rightarrow> resource set" where
"resources p \<equiv> {r | r. \<forall>i. i < snd (p_handles p) \<and> fst (p_handles p) i = Some r }"

text\<open>From the system state, find a resource and return its security context\<close>

fun resource_sec_ctxt :: "state \<Rightarrow> resource \<Rightarrow> SecCtxt option" where
"resource_sec_ctxt s (Window n) = (case fst (windows s) n of
    None \<Rightarrow> None
  | Some w \<Rightarrow> Some (w_sc w))" |
"resource_sec_ctxt s (Object n) = (case fst (objects s) n of
    None \<Rightarrow> None
  | Some obj \<Rightarrow> Some (obj_sc obj))" |
"resource_sec_ctxt s _ = None"

definition must_dominate :: "state \<Rightarrow> proc \<Rightarrow> resource \<Rightarrow> bool" where
"must_dominate s p r \<equiv> \<exists>n. resource_sec_ctxt s r = Some n \<and> dominates (p_sc p) n"

definition enforces_policy :: "state \<Rightarrow> bool" where
"enforces_policy s \<equiv> \<forall>subj obj. subj \<in> subjects s \<and> obj \<in> resources subj \<longrightarrow> must_dominate s subj obj"
 
text\<open>Evolution of the system state is required to satisfy some invariants, collected in the below
definition.\<close>

definition invs :: "state \<Rightarrow> bool" where
"invs s \<equiv> pid_bound s \<and> valid_caller s \<and> valid_servers s \<and> enforces_policy s"

text\<open>An admissible event is well-formed: executed by a valid process and all the arguments to the
operation satisfy required preconditions. These checks do not handle security relevant
preconditions.\<close>

inductive admissible :: "state \<Rightarrow> event \<Rightarrow> bool" where
admit_ProcCreate: "\<lbrakk> valid_pid i s \<rbrakk> \<Longrightarrow> admissible s (Syscall i (ProcCreate _))" |
admit_WindowCreate: "\<lbrakk> valid_pid i s \<rbrakk> \<Longrightarrow> admissible s (Syscall i (WindowCreate b sz))" |
admit_ObjCreate:"\<lbrakk> valid_pid i s ; valid_server_endpoint s i ep \<rbrakk> \<Longrightarrow> admissible s (Syscall i (ObjCreate ep attr sz sc))" |
admit_ConnPublish: "\<lbrakk> valid_pid i s ; free_cslot s i k \<rbrakk> \<Longrightarrow> admissible s (Syscall i (ConnPublish k n))"

declare admissible.intros [intro]

inductive_cases admit_ProcCreateE[elim!]:"admissible s (Syscall i (ProcCreate sc))"
inductive_cases admit_WindowCreateE[elim!]:"admissible s (Syscall i (WindowCreate b sz))"
inductive_cases admit_ConnPublishE[elim!]:"admissible s (Syscall i (ConnPublish k n))"

inductive authorised :: "state \<Rightarrow> event \<Rightarrow> bool" where
auth_ProcCreate: "\<lbrakk> dominates (get_sec_ctxt s i) sc \<rbrakk> \<Longrightarrow> authorised s (Syscall i (ProcCreate sc))" |
auth_WindowCreate: "authorised s (Syscall i (WindowCreate b sz))" |
auth_ConnPublish: "\<lbrakk> n \<in> auth_servers s ; get_server s n = None \<rbrakk> \<Longrightarrow> authorised s (Syscall i (ConnPublish k n))"

declare authorised.intros [intro]

inductive_cases auth_ProcCreateE[elim!]:"authorised s (Syscall i (ProcCreate sc))"
inductive_cases auth_WindowCreateE[elim!]:"authorised s (Syscall i (WindowCreate b sz))"
inductive_cases auth_ConnPublishE[elim!]:"authorised s (Syscall i (ConnPublish k n))"

end