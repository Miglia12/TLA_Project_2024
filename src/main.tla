------------------------------ MODULE main ------------------------------
EXTENDS Integers, Sequences

VARIABLES Data,      \* The set of all possible data values.
          Cpu,       \* The record containing the state and the value.
          logical_segments,    \* The map of memorys keyed by gpu_id.
          KGpus,      \* The record representing the KGpus entities.
          PushChannel \* One way message channel from GPU to CPU.

CONSTANTS NULL,      \* Placeholder for the empty value
          ACK,       \* Placeholder for the ack value
          StatesCpu, \* The set of all possible CPU states
          StatesGpu, \* The set of all possible GPU states
          MAX_INT_VALUE, \* The ceiling for all data values
          N_KGPU

-------------------------------------------------------------------------
(***************************************************************************)
(* Helper function to check if an element is not in a sequence.            *)
(***************************************************************************)
NotInSeq(elem, seq) == \A i \in 1..Len(seq) : elem # seq[i]

(***************************************************************************)
(* Helper function to find the index of an element in a sequence.          *)
(***************************************************************************)
IndexOf(elem, seq) == 
    CHOOSE i \in 1..Len(seq) : seq[i] = elem

(***************************************************************************)
(* Helper function to remove the first occurrence of an element            *)
(* from a sequence.                                                        *)
(***************************************************************************)
RemoveFromSeq(elem, seq) == 
    IF ~ \E i \in 1..Len(seq) : seq[i] = elem THEN seq
    ELSE [i \in 1..(Len(seq) - 1) |-> 
            IF i < IndexOf(elem, seq) THEN seq[i]
            ELSE seq[i + 1]
         ]
-------------------------------------------------------------------------------------------- 

(***************************************************************************)
(* TypeOK defines the types of the variables to ensure their correctness.  *)
(* - Data: A set of integers within the range 0 to MAX_INT_VALUE excluding ACK. *)
(* - Cpu: A record with fields:                                              *)
(*   - state: Represents the state of the CPU, which can be "idle",          *)
(*     "processing", "fetching", or "sending".                               *)
(*   - value: Can be NULL or an integer within the range 0 to MAX_INT_VALUE  *)
(*     excluding ACK.                                                        *)
(*   - subs_map: A mapping from each KGPU to an integer within the range     *)
(*     0 to MAX_INT_VALUE.                                                   *)
(*   - subs_list: A sequence of integers representing KGpus.                 *)
(* - logical_segments: A mapping from each KGPU to a sequence of elements    *)
(*   that can be ACK or in Data.                                             *)
(* - KGpus: A mapping from each KGPU to a record with fields:                 *)
(*   - id: An identifier within the range 1 to N_KGPU.                       *)
(*   - state: Represents the state of the GPU, which can be "idle",          *)
(*     "requesting", "working", or "waiting".                                *)
(*   - missing_data: An integer within the range 3 to MAX_INT_VALUE.         *)
(*   - memory: A sequence of elements in Data.                               *)
(* - PushChannel: A sequence of records, each containing:                    *)
(*   - id: An identifier within the range 1 to N_KGPU.                       *)
(*   - numData: An integer within the range 3 to MAX_INT_VALUE.              *)
(***************************************************************************)
TypeOK == /\ Data \subseteq 0..MAX_INT_VALUE \ {ACK}
          /\ Cpu \in [ state : {"idle", "processing", "fetching", "sending"},
                      value : {NULL} \cup (0..MAX_INT_VALUE \ {ACK}),
                      subs_map : [1..N_KGPU -> 0..MAX_INT_VALUE],
                      subs_list : Seq(1..N_KGPU) ]
          /\ logical_segments \in [1..N_KGPU -> Seq({ACK} \cup Data)]
          /\ KGpus \in [1..N_KGPU -> [ id : 1..N_KGPU,
                                      state : {"idle", "requesting", "working", "waiting"},
                                      missing_data : 0..MAX_INT_VALUE,
                                      memory : Seq(Data) ]]
          /\ PushChannel \in Seq([id : 1..N_KGPU, numData : 3..MAX_INT_VALUE])

vars == << Data, Cpu, logical_segments, KGpus, PushChannel >>

(***************************************************************************)
(* Init defines the initial state of the system.                           *)
(* - Data: Initialized to the range from ACK + 1 to MAX_INT_VALUE.         *)
(* - Cpu: Initialized with:                                                *)
(*   - state: Set to "idle".                                               *)
(*   - value: Set to NULL.                                                 *)
(*   - subs_map: Each KGPU is mapped to 0.                                 *)
(*   - subs_list: An empty sequence.                                       *)
(* - logical_segments: Each KGPU is mapped to an empty sequence.           *)
(* - KGpus: Each KGPU is initialized with:                                 *)
(*   - id: Set to its corresponding identifier.                            *)
(*   - state: Set to "idle".                                               *)
(*   - missing_data: Set to a value chosen within the range 3 to           *)
(*     MAX_INT_VALUE.                                                      *)
(*   - memory: An empty sequence.                                          *)
(* - PushChannel: Initialized to an empty sequence.                       *)
(***************************************************************************)
Init == /\ Data = ACK + 1..MAX_INT_VALUE
        /\ Cpu = [  state |-> "idle", 
                    value |-> NULL, 
                    subs_map |-> [i \in 1..N_KGPU |-> 0], 
                    subs_list |-> <<>>]
        /\ logical_segments = [i \in 1..N_KGPU |-> <<>>]
        /\ KGpus = [i \in 1..N_KGPU |-> [ id |-> i, 
                                          state |-> "idle", 
                                          missing_data |-> CHOOSE x \in 3..MAX_INT_VALUE : TRUE, 
                                          memory |-> <<>>]]
        /\ PushChannel = <<>>

(***************************************************************************)
(* ReceiveMsg_CPU handles the reception of a message by the CPU.           *)
(* - Cpu.state: Must be "idle".                                            *)
(* - PushChannel: Must not be empty.                                       *)
(* - msg: Is the first element of PushChannel.                     *)
(* - Cpu': Updated with:                                                   *)
(*   - state: Set to "processing".                                         *)
(*   - subs_map: The entry for msg.id is updated to msg.numData.           *)
(*   - subs_list: msg.id is appended to the list.                          *)
(* - PushChannel': The read message gets removed.                         *)
(* - logical_segments': The segment for msg.id is updated by appending ACK.*)
(***************************************************************************)
ReceiveMsg_CPU == /\ Cpu.state = "idle"
                  /\ PushChannel # <<>>
                  /\ LET msg == Head(PushChannel) IN
                    /\ Cpu' = [Cpu EXCEPT 
                                !.state = "processing", 
                                !.subs_map[msg.id] = msg.numData, 
                                !.subs_list = Append(Cpu.subs_list, msg.id)]
                    /\ PushChannel' = Tail(PushChannel)
                    /\ logical_segments' = [logical_segments EXCEPT ![msg.id] = Append(@, ACK)]
                  /\ UNCHANGED <<KGpus, Data>>

(***************************************************************************)
(* FetchData_CPU defines the conditions and actions for fetching data by the CPU. *)
(* - Cpu:                                                                  *)
(*   - state: Must be "idle".                                              *)
(*   - subs_list: Must not be empty.                                       *)
(*   - value: Must be NULL.                                                *)
(* - gpu_id: The head of Cpu.subs_list.                                    *)
(*   - Cpu.subs_map[gpu_id]: Must be greater than 0. This means that the   *)
(*                          GPU still needs some data.                     *)
(* - d: Chosen from Data.                                                  *)
(*   - Cpu': Updated with:                                                 *)
(*     - state: Set to "fetching".                                         *)
(*     - value: Set to d.                                                  *)
(***************************************************************************)
FetchData_CPU == 
        /\ Cpu.state = "idle"
        /\ Cpu.subs_list # <<>>
        /\ Cpu.value = NULL
        /\ LET gpu_id == Head(Cpu.subs_list) IN
            IF Cpu.subs_map[gpu_id] # 0 THEN 
                /\ LET d == CHOOSE x \in Data : TRUE IN
                    /\ Cpu' = [Cpu EXCEPT !.state = "fetching", !.value = d]
                /\ UNCHANGED <<logical_segments, KGpus, Data, PushChannel>>
            ELSE
                /\ Cpu' = [Cpu EXCEPT !.subs_list = Tail(@)]
                /\ UNCHANGED <<KGpus, PushChannel, Data, logical_segments, Cpu.state, Cpu.value, Cpu.subs_map>>

(***************************************************************************)
(* SendData_CPU defines the transition for sending data by the CPU.        *)
(* - Cpu.state: Must be "idle".                                            *)
(* - Cpu.value: Must not be NULL.                                          *)
(* - LET gpu_id: The first element in Cpu.subs_list.                       *)
(*   - If Cpu.subs_map[gpu_id] = 0:                                        *)
(*     - Then the KGPU gets unsuscribed since all data has been delivered. *)
(*   - ELSE:                                                               *)
(*     - Send the data to the KGPU                                         *)
(*     - Cpu':                                                             *)
(*       - state: Set to "sending".                                        *)
(*       - value: Set to NULL.                                             *)
(*       - subs_map[gpu_id]: Decrement by 1.                               *)
(*     - Cpu'.subs_list: Append gpu_id to the tail of Cpu.subs_list.       *)
(***************************************************************************)
SendData_CPU == 
    /\ Cpu.state = "idle"
    /\ Cpu.value # NULL
    /\ LET gpu_id == Head(Cpu.subs_list) IN
        /\ logical_segments' = [logical_segments EXCEPT ![gpu_id] = Append(@, Cpu.value)]
        /\ Cpu' = 
            [ Cpu EXCEPT 
                !.state = "sending", 
                !.value = NULL, 
                !.subs_map[gpu_id] = @ - 1,
                !.subs_list = Append(Tail(@), gpu_id)
            ]
    /\ UNCHANGED <<KGpus, PushChannel, Data>>

(***************************************************************************)
(* Action Idle_CPU makes the CPU idle after every action.                  *)
(***************************************************************************)
Idle_CPU ==    /\ Cpu.state \in {"fetching", "sending", "processing"}
               /\ Cpu' = [Cpu EXCEPT !.state = "idle"]
               /\ UNCHANGED <<logical_segments, KGpus, Data, PushChannel>>

(***************************************************************************)
(* Action Subscribe_GPU defines a GPU sending a message to the CPU and     *)
(* transitioning to "requesting" state.                                    *)
(* The CPU will receive that message and immediatly send an ack.           *)
(* The value "numData" is the number of data items the CPU will have to    *)
(* fetch. The value "id" is a unique identifier for each GPU.              *)
(***************************************************************************)
\* Assuming that the request will not be lost.
Subscribe_GPU == /\ \E gpu_id \in 1..N_KGPU : 
                    /\ KGpus[gpu_id].state = "idle"
                    /\ logical_segments[gpu_id] = <<>>       
                    /\ LET msg == [id |-> gpu_id, numData |-> KGpus[gpu_id].missing_data] IN
                      /\ PushChannel' = Append(PushChannel, msg)
                      /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "requesting"]
                 /\ UNCHANGED <<logical_segments, Cpu, Data>>
                 

(***************************************************************************)
(* Action RcvACK_GPU defines a GPU receiving the ack form the cpu          *)
(* transitioning to "waiting" state.                                       *)
(***************************************************************************)                 
RcvACK_GPU == /\ \E gpu_id \in 1..N_KGPU : 
                    /\ KGpus[gpu_id].state = "requesting"
                    /\ logical_segments[gpu_id] # <<>>
                    /\ LET required_data == Head(logical_segments[gpu_id]) IN
                        /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "waiting"] 
                    /\ logical_segments' = [logical_segments EXCEPT ![gpu_id] = Tail(@)]               
                    /\ UNCHANGED <<Cpu, Data, PushChannel>>

(***************************************************************************)
(* Action RcvData_GPU defines a GPU transitioning to "working" state.      *)
(* The GPU accessing the first element of its respective memory,           *)
(* storing it in its own memory, and removing it from the logica segment.  *)
(***************************************************************************)
RcvData_GPU ==  /\ \E gpu_id \in 1..N_KGPU :
                    /\ KGpus[gpu_id].state = "waiting"
                    /\ logical_segments[gpu_id] # <<>>
                    /\ LET required_data == Head(logical_segments[gpu_id]) IN
                            /\ KGpus' = [KGpus EXCEPT 
                                            ![gpu_id].memory = Append(KGpus[gpu_id].memory, required_data), 
                                            ![gpu_id].state = "working", 
                                            ![gpu_id].missing_data = @ - 1]                 
                    /\ logical_segments' = [logical_segments EXCEPT ![gpu_id] = Tail(@)]
                    /\ UNCHANGED <<Cpu, Data, PushChannel>>

(***************************************************************************)
(* Action Waiting_GPU signals a GPU which is waiting for the data.         *)
(***************************************************************************)
Waiting_GPU ==  /\ \E gpu_id \in 1..N_KGPU :
                    /\ KGpus[gpu_id].state = "working"
                    /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "waiting"]
                    /\ UNCHANGED <<logical_segments, Cpu, Data, PushChannel>>

(***************************************************************************)
(* Next defines the possible next actions in the system.                   *)
(***************************************************************************)
Next ==     \/ ReceiveMsg_CPU 
            \/ FetchData_CPU 
            \/ SendData_CPU 
            \/ Idle_CPU 
            \/ Subscribe_GPU 
            \/ RcvACK_GPU
            \/ RcvData_GPU 
            \/ Waiting_GPU

(***************************************************************************)
(* The overall specification, Spec, starts with Init and requires that     *)
(* Next is always enabled.                                                 *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* FairSpec is Spec with the additional requirement that it keeps taking   *)
(* steps.                                                                  *)
(***************************************************************************)
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Define the temporal property that eventually all data will be in the    *)
(* GPU memory.                                                             *)
(***************************************************************************)
AllDataInGpu == <> (\A gpu_id \in 1..N_KGPU : logical_segments[gpu_id] = <<>> /\ KGpus[gpu_id].memory # <<>>)

==========================================================================
