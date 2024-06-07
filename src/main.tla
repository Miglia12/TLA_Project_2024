------------------------------ MODULE main ------------------------------
EXTENDS Integers, Sequences

VARIABLES Cpu,       \* The record containing the state and the value.
          Streamlets,
          LogicalSegments,    \* The map of memorys keyed by gpu_id.
          KGpus,      \* The record representing the KGpus entities.
          PushChannel \* One way message channel from GPU to CPU.
          
CONSTANTS NULL,      \* Placeholder for the empty value
          ACK,       \* Placeholder for the ack value
          MAX_INT_VALUE, \* The ceiling for all data values
          N_KGPU,    \* Number of KGpus
          N_STREAMLETS, \* Number of streamlets
          IntType \* The set of all possible data values (0..MAX_INT_VALUE)
          
(***************************************************************************)
(* Type definition for Cpu.                                                *)
(***************************************************************************)
CpuType == [ state : {"idle", "processing", "computing", "sending"},
             value : {NULL} \cup Int,
             subs : Seq([kgpu_id : 0..N_KGPU, required_data : IntType]) ]

(***************************************************************************)
(* Type definition for LogicalSegments.                                   *)
(***************************************************************************)
LogicalSegmentsType == [0..N_KGPU -> Seq({ACK} \cup IntType)]

(***************************************************************************)
(* Type definition for a KGpu.                                             *)
(***************************************************************************)
KGpuType == [ id : 0..N_KGPU,
              state : {"idle", "requesting", "working", "waiting"},
              missing_data : IntType,
              memory : Seq(IntType) ]

(***************************************************************************)
(* Type definition for the collection of KGpus.                            *)
(***************************************************************************)
KGpusType == [0..N_KGPU -> KGpuType]

(***************************************************************************)
(* Type definition for PushChannel.                                        *)
(***************************************************************************)
PushChannelType == Seq([id : 0..N_KGPU, numData : IntType])

(***************************************************************************)
(* Type definition for a streamlet.                                        *)
(***************************************************************************)
StreamletType == [ start_address : Int,
                   stop_address : Int,
                   kgpu_id : Int,
                   current_address : Int ]

(***************************************************************************)
(* Type definition for the collection of streamlets.                       *)
(***************************************************************************)
StreamletsType == [0..N_STREAMLETS -> StreamletType]

(***************************************************************************)
(* TypeOK *)
(***************************************************************************)
TypeOK == /\ NULL \notin IntType
          /\ ACK \notin IntType
          /\ Cpu \in CpuType
          /\ Streamlets \in StreamletsType
          /\ LogicalSegments \in LogicalSegmentsType
          /\ KGpus \in KGpusType
          /\ PushChannel \in PushChannelType

vars == << Cpu, Streamlets, LogicalSegments, KGpus, PushChannel>>

(***************************************************************************)
(* Init defines the initial state of the system.                           *)
(* - IntType: Initialized to the range from 0 to MAX_INT_VALUE excluding ACK. *)
(* - Cpu: Initialized with:                                                *)
(*   - state: Set to "idle".                                               *)
(*   - value: Set to NULL.                                                 *)
(*   - subs: An empty sequence.                                            *)
(* - LogicalSegments: Each KGPU is mapped to an empty sequence.           *)
(* - KGpus: Each KGPU is initialized with:                                 *)
(*   - id: Set to its corresponding identifier.                            *)
(*   - state: Set to "idle".                                               *)
(*   - missing_data: Set to a value chosen within the range 3 to           *)
(*     MAX_INT_VALUE, excluding 0.                                         *)
(*   - memory: An empty sequence.                                          *)
(* - PushChannel: Initialized to an empty sequence.                       *)
(* - streamlets: Each streamlet is initialized with:                       *)
(*   - start_address: Set to 0.                                            *)
(*   - stop_address: Set to 0.                                             *)
(*   - kgpu_id: Set to 0.                                                  *)
(*   - current_address: Set to 1.                                          *)
(***************************************************************************)
Init == /\ Cpu = [ state |-> "idle", 
                   value |-> NULL, 
                   subs |-> <<>> ]
        /\ Streamlets = [i \in 0..N_STREAMLETS |-> [ start_address |-> 0, 
                                                     stop_address |-> 0, 
                                                     kgpu_id |-> 0,
                                                     current_address |-> 1 ]]
        /\ LogicalSegments = [i \in 0..N_KGPU |-> <<>>]
        /\ KGpus = [i \in 0..N_KGPU |-> [ id |-> i, 
                                          state |-> "idle", 
                                          missing_data |-> CHOOSE x \in 0..MAX_INT_VALUE : x > 2, 
                                          memory |-> <<>>]]
        /\ PushChannel = <<>>

(***************************************************************************)
(* ReceiveMsg_CPU handles the reception of a message by the CPU.           *)
(* - Cpu.state: Must be "idle".                                            *)
(* - PushChannel: Must not be empty.                                       *)
(* - msg: Is the first element of PushChannel.                             *)
(* - Cpu': Updated with:                                                   *)
(*   - state: Set to "processing".                                         *)
(*   - subs: Appends a record with msg.id and msg.numData.                 *)
(* - PushChannel': The read message gets removed.                         *)
(* - LogicalSegments': The segment for msg.id is updated by appending ACK.*)
(***************************************************************************)
ReceiveMsg_CPU == /\ Cpu.state = "idle"
                  /\ PushChannel # <<>>
                  /\ LET msg == Head(PushChannel) IN
                    /\ Cpu' = [Cpu EXCEPT 
                                !.state = "processing", 
                                !.subs = Append(Cpu.subs, [kgpu_id |-> msg.id, required_data |-> msg.numData])]
                    /\ PushChannel' = Tail(PushChannel)
                    /\ LogicalSegments' = [LogicalSegments EXCEPT ![msg.id] = Append(@, ACK)]
                  /\ UNCHANGED <<KGpus, Streamlets>>

(***************************************************************************)
(* ComputeDataLocation_CPU defines the conditions and actions for computing data by the CPU. *)
(* - Cpu:                                                                  *)
(*   - state: Must be "idle".                                              *)
(*   - subs: Must not be empty.                                            *)
(*   - value: Must be NULL.                                                *)
(* - kgpu_id: The head of Cpu.subs.                                        *)
(*   - required_data: The segment to be streamed.                      *)
(*   - Cpu.subs: The entry for kgpu_id is checked.                         *)
(*   - d: Chosen from IntType.                                             *)
(*   - Cpu': Updated with:                                                 *)
(*     - state: Set to "computing".                                         *)
(*     - value: Set to d.                                                  *)
(***************************************************************************)
ComputeDataLocation_CPU == 
        /\ Cpu.state = "idle"
        /\ Cpu.subs # <<>>
        /\ Cpu.value = NULL
        /\ LET sub == Head(Cpu.subs) IN
            IF sub.required_data # 0 THEN 
                /\ LET d == CHOOSE x \in IntType : TRUE  IN
                    /\ Cpu' = [Cpu EXCEPT !.state = "computing", !.value = d]
                /\ UNCHANGED <<LogicalSegments, KGpus, IntType, PushChannel, Streamlets>>
            ELSE
                /\ Cpu' = [Cpu EXCEPT !.subs = Tail(@)]
                /\ UNCHANGED <<KGpus, PushChannel, LogicalSegments, Cpu.state, Cpu.value, Streamlets>>

(***************************************************************************)
(* StartStream_CPU defines the transition for sending data by the CPU.        *)
(* - Cpu.state: Must be "idle".                                            *)
(* - Cpu.value: Must not be NULL.                                          *)
(* - LET sub: The first element in Cpu.subs.                               *)
(*   - If sub.required_data = 0:                                           *)
(*     - Then the KGPU gets unsubscribed since all data has been delivered. *)
(*   - ELSE:                                                               *)
(*     - Send the data to the KGPU                                         *)
(*     - Cpu':                                                             *)
(*       - state: Set to "sending".                                        *)
(*       - value: Set to NULL.                                             *)
(*       - subs: The entry for kgpu_id is updated.                         *)
(***************************************************************************)
StartStream_CPU == 
    /\ Cpu.state = "idle"
    /\ Cpu.value # NULL
    /\ \E s \in DOMAIN Streamlets : Streamlets[s].current_address >= Streamlets[s].stop_address
    /\ LET streamlet == CHOOSE s \in DOMAIN Streamlets : Streamlets[s].current_address >= Streamlets[s].stop_address IN
        /\ LET sub == Head(Cpu.subs) IN
            /\ Streamlets' = [Streamlets EXCEPT 
                                ![streamlet].start_address = Cpu.value,
                                ![streamlet].stop_address = Cpu.value + sub.required_data,
                                ![streamlet].kgpu_id = sub.kgpu_id,
                                ![streamlet].current_address = Cpu.value]
            /\ Cpu' = [Cpu EXCEPT 
                        !.state = "sending", 
                        !.value = NULL,
                        !.subs = Tail(@)
                      ]
    /\ UNCHANGED <<KGpus, PushChannel, LogicalSegments>>

(***************************************************************************)
(* Action Idle_CPU makes the CPU idle after every action.                  *)
(***************************************************************************)
Idle_CPU ==    /\ Cpu.state \in {"computing", "sending", "processing"}
               /\ Cpu' = [Cpu EXCEPT !.state = "idle"]
               /\ UNCHANGED <<LogicalSegments, KGpus, PushChannel, Streamlets>>
               

(* Define a stream if there exists a streamlet that is in the streaming state *)
Stream ==  
    /\ \E s \in DOMAIN Streamlets : Streamlets[s].current_address < Streamlets[s].stop_address
    /\ LET streamlet == CHOOSE s \in DOMAIN Streamlets : Streamlets[s].current_address < Streamlets[s].stop_address IN
        /\ LET data == CHOOSE x \in IntType : TRUE IN
            /\ LogicalSegments' = [LogicalSegments EXCEPT ![Streamlets[streamlet].kgpu_id] = Append(LogicalSegments[Streamlets[streamlet].kgpu_id], data)]
            /\ Streamlets' = 
                [Streamlets EXCEPT 
                    ![streamlet].current_address = Streamlets[streamlet].current_address + 1]
    /\ UNCHANGED <<Cpu, KGpus, PushChannel>>

(***************************************************************************)
(* Action Subscribe_GPU defines a GPU sending a message to the CPU and     *)
(* transitioning to "requesting" state.                                    *)
(* The CPU will receive that message and immediately send an ack.          *)
(* The value "numData" is the number of data items the CPU will have to    *)
(* fetch. The value "id" is a unique identifier for each GPU.              *)
(***************************************************************************)
\* Assuming that the request will not be lost.
Subscribe_GPU == /\ \E gpu_id \in 1..N_KGPU : 
                    /\ KGpus[gpu_id].state = "idle"
                    /\ LogicalSegments[gpu_id] = <<>>       
                    /\ LET msg == [id |-> gpu_id, numData |-> KGpus[gpu_id].missing_data] IN
                      /\ PushChannel' = Append(PushChannel, msg)
                      /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "requesting"]
                 /\ UNCHANGED <<LogicalSegments, Cpu, Streamlets>>

(***************************************************************************)
(* Action RcvACK_GPU defines a GPU receiving the ack form the cpu          *)
(* transitioning to "waiting" state.                                       *)
(***************************************************************************)                 
RcvACK_GPU == /\ \E gpu_id \in 1..N_KGPU : 
                    /\ KGpus[gpu_id].state = "requesting"
                    /\ LogicalSegments[gpu_id] # <<>>
                    /\ LET required_data == Head(LogicalSegments[gpu_id]) IN
                        /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "waiting"] 
                    /\ LogicalSegments' = [LogicalSegments EXCEPT ![gpu_id] = Tail(@)]               
                    /\ UNCHANGED <<Cpu, PushChannel, Streamlets>>

(***************************************************************************)
(* Action RcvData_GPU defines a GPU transitioning to "working" state.      *)
(* The GPU accessing the first element of its respective memory,           *)
(* storing it in its own memory, and removing it from the logical segment. *)
(***************************************************************************)
RcvData_GPU ==  /\ \E gpu_id \in 1..N_KGPU :
                    /\ KGpus[gpu_id].state = "waiting"
                    /\ LogicalSegments[gpu_id] # <<>>
                    /\ LET required_data == Head(LogicalSegments[gpu_id]) IN
                            /\ KGpus' = [KGpus EXCEPT 
                                            ![gpu_id].memory = Append(KGpus[gpu_id].memory, required_data), 
                                            ![gpu_id].state = "working", 
                                            ![gpu_id].missing_data = @ - 1]                 
                    /\ LogicalSegments' = [LogicalSegments EXCEPT ![gpu_id] = Tail(@)]
                    /\ UNCHANGED <<Cpu, PushChannel, Streamlets>>

(***************************************************************************)
(* Action Waiting_GPU signals a GPU which is waiting for the data.         *)
(***************************************************************************)
Waiting_GPU ==  /\ \E gpu_id \in 1..N_KGPU :
                    /\ KGpus[gpu_id].state = "working"
                    /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "waiting"]
                    /\ UNCHANGED <<LogicalSegments, Cpu, PushChannel, Streamlets>>

(***************************************************************************)
(* Next defines the possible next actions in the system.                   *)
(***************************************************************************)
Next ==     \/ ReceiveMsg_CPU 
            \/ ComputeDataLocation_CPU 
            \/ StartStream_CPU 
            \/ Idle_CPU 
            \/ Stream
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
AllDataInGpu == <> (\A gpu_id \in 1..N_KGPU : LogicalSegments[gpu_id] = <<>> /\ KGpus[gpu_id].memory # <<>>)

==========================================================================
