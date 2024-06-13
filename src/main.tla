------------------------------ MODULE main ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS NULL,                 \* Placeholder for the empty value
          ACK,                  \* Placeholder for the acknowledgement value
          N_KGPU,               \* Number of KGpus
          N_STREAMLETS,         \* Number of streamlets
          LOGICAL_SEGMENT_SIZE, \* Number of slots in each logical segment
          DataType,             \* Set of all possible data values
          BoundedInt    

VARIABLES Cpu,              \* Record rapresenting the CPU
          Streamlets,       \* Collection of streamlets
          LogicalSegments,  \* Map of memory slots one for each GPU Kernel
          KGpus,            \* Record representing the GPU Kernels
          PushChannel       \* One-way message channel from GPU to CPU
          
--------------------------------------------------------------------------
(***************************************************************************)
(* FindEmptySlot:                                                           *)
(* Returns the index of the first occurrence of NULL or 0 if none is found.*)
(***************************************************************************)
FindEmptySlot(id, LogicalSegmentsMap) == 
    LET segment == LogicalSegments[id] IN
        IF \E idx \in 1..LOGICAL_SEGMENT_SIZE : segment[idx] = NULL
        THEN CHOOSE idx \in 1..LOGICAL_SEGMENT_SIZE : segment[idx] = NULL
        ELSE 0
        
(***************************************************************************)
(* FindDataSlot                                                     *)
(* Returns the index of the first occurrence of a non-NULL element or 0    *)
(* if all elements are NULL.                                               *)
(***************************************************************************)
FindDataSlot(id, LogicalSegmentsMap) == 
    LET segment == LogicalSegmentsMap[id] IN
        IF \E idx \in 1..LOGICAL_SEGMENT_SIZE : segment[idx] # NULL
        THEN CHOOSE idx \in 1..LOGICAL_SEGMENT_SIZE : segment[idx] # NULL
        ELSE 0
        
(***************************************************************************)
(* FindACKSlot:                                                           *)
(* Returns the index of the first occurrence of ACK or 0 if none is found. *)
(***************************************************************************)
FindACKSlot(id, LogicalSegmentsMap) ==
    LET segment == LogicalSegmentsMap[id] IN
        IF \E idx \in 1..LOGICAL_SEGMENT_SIZE : segment[idx] = ACK
        THEN CHOOSE idx \in 1..LOGICAL_SEGMENT_SIZE : segment[idx] = ACK
        ELSE 0
--------------------------------------------------------------------------

(***************************************************************************)
(* Type definition for Cpu.                                                *)
(***************************************************************************)
CpuType == [ state : {"idle", "processing", "computing", "sending"},
             value : {NULL} \cup Int,
             subs : Seq([kgpu_id : 1..N_KGPU, required_data : Int]) ]

(***************************************************************************)
(* Type definition for LogicalSegments.                                   *)
(***************************************************************************)
LogicalSegmentsType == [1..N_KGPU -> [1..LOGICAL_SEGMENT_SIZE -> DataType \cup {ACK, NULL}]]

(***************************************************************************)
(* Type definition for a KGpu.                                             *)
(***************************************************************************)
KGpuType == [ id : 1..N_KGPU,
              state : {"idle", "requesting", "working", "waiting", "done"},
              missing_data : Int,
              memory : Seq(DataType) ]

(***************************************************************************)
(* Type definition for the collection of KGpus.                            *)
(***************************************************************************)
KGpusType == [1..N_KGPU -> KGpuType]

(***************************************************************************)
(* Type definition for PushChannel.                                        *)
(***************************************************************************)
PushChannelType == Seq([id : 1..N_KGPU, requiredData : Int])

(***************************************************************************)
(* Type definition for a streamlet.                                        *)
(***************************************************************************)
StreamletType == [ start_address : Int,
                   stop_address : Int,
                   kgpu_id : 1..N_KGPU,
                   current_address : Int ]

(***************************************************************************)
(* Type definition for the collection of streamlets.                       *)
(***************************************************************************)
StreamletsType == [1..N_STREAMLETS -> StreamletType]

(***************************************************************************)
(* TypeOK *)
(***************************************************************************)
TypeOK == /\ NULL \notin Int
          /\ ACK \notin Int
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
Init == 
    /\ Cpu = [ state |-> "idle", 
               value |-> NULL, 
               subs |-> <<>> ]

    /\ Streamlets = [i \in 1..N_STREAMLETS |-> 
                     [ start_address |-> 0, 
                       stop_address |-> 0, 
                       kgpu_id |-> 1, 
                       current_address |-> 1 ]]

    /\ LogicalSegments = [i \in 1..N_KGPU |-> 
                          [j \in 1..LOGICAL_SEGMENT_SIZE |-> NULL]]

    /\ KGpus = [i \in 1..N_KGPU |-> 
                [ id |-> i, 
                  state |-> "idle", 
                  missing_data |-> RandomElement(BoundedInt), 
                  memory |-> <<>>]]

    /\ PushChannel = <<>>

(***************************************************************************)
(* ReceiveMsg_CPU handles the reception of a message by the CPU.           *)
(* - Cpu.state: Must be "idle".                                            *)
(* - PushChannel: Must not be empty.                                       *)
(* - msg: Is the first element of PushChannel.                             *)
(* - Cpu': Updated with:                                                   *)
(*   - state: Set to "processing".                                         *)
(*   - subs: Appends a record with msg.id and msg.requiredData.                 *)
(* - PushChannel': The read message gets removed.                         *)
(* - LogicalSegments': The segment for msg.id is updated by appending ACK.*)
(***************************************************************************)
ReceiveMsg_CPU ==
    /\ Cpu.state = "idle"
    /\ PushChannel # <<>>
    /\ LET
        msg == Head(PushChannel)
        idx == FindEmptySlot(msg.id, LogicalSegments)
       IN
        /\ idx > 0
        /\ Cpu' = [Cpu EXCEPT 
                    !.state = "processing", 
                    !.subs = Append(Cpu.subs, [kgpu_id |-> msg.id, required_data |-> msg.requiredData])]
        /\ LogicalSegments' = [LogicalSegments EXCEPT ![msg.id][idx] = ACK]
        /\ PushChannel' = Tail(PushChannel)
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
    /\ LET
        sub == Head(Cpu.subs)
        address == RandomElement(BoundedInt)
       IN
        IF sub.required_data # 0 THEN
            /\ Cpu' = [Cpu EXCEPT !.state = "computing", !.value = address]
            /\ UNCHANGED <<LogicalSegments, KGpus, PushChannel, Streamlets>>
        ELSE
            /\ Cpu' = [Cpu EXCEPT !.subs = Tail(Cpu.subs)]
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
    /\ \E streamlet \in DOMAIN Streamlets : 
            /\ Streamlets[streamlet].current_address >= Streamlets[streamlet].stop_address
            /\ LET
                sub == Head(Cpu.subs)
                new_start_address == Cpu.value
                new_stop_address == Cpu.value + sub.required_data
                new_current_address == Cpu.value
                new_kgpu_id == sub.kgpu_id
              IN
                /\ Streamlets' = [Streamlets EXCEPT 
                                    ![streamlet].start_address = new_start_address,
                                    ![streamlet].stop_address = new_stop_address,
                                    ![streamlet].kgpu_id = new_kgpu_id,
                                    ![streamlet].current_address = new_current_address]
                /\ Cpu' = [Cpu EXCEPT 
                            !.state = "sending", 
                            !.value = NULL,
                            !.subs = Tail(@)]
    /\ UNCHANGED <<KGpus, PushChannel, LogicalSegments>>

(***************************************************************************)
(* Action Idle_CPU makes the CPU idle after every action.                  *)
(***************************************************************************)
Idle_CPU == 
    /\ Cpu.state \in {"computing", "sending", "processing"}
    /\ Cpu' = [Cpu EXCEPT !.state = "idle"]                  
    /\ UNCHANGED <<LogicalSegments, KGpus, PushChannel, Streamlets>>
               

(* Define a stream if there exists a streamlet that is in the streaming state *)
Stream ==  
    \E s \in DOMAIN Streamlets :
        LET
            streamlet == CHOOSE str \in DOMAIN Streamlets : Streamlets[str].current_address < Streamlets[str].stop_address
            idx == FindEmptySlot(Streamlets[streamlet].kgpu_id, LogicalSegments)
            data == CHOOSE x \in DataType : TRUE
        IN
            /\ Streamlets[s].current_address < Streamlets[s].stop_address
            /\ idx > 0 
            /\ LogicalSegments' = 
                [LogicalSegments EXCEPT 
                    ![Streamlets[streamlet].kgpu_id][idx] = data]
            /\ Streamlets' = 
                [Streamlets EXCEPT 
                    ![streamlet].current_address = Streamlets[streamlet].current_address + 1]
            /\ UNCHANGED <<Cpu, KGpus, PushChannel>>

(***************************************************************************)
(* Action Subscribe_GPU defines a GPU sending a message to the CPU and     *)
(* transitioning to "requesting" state.                                    *)
(* The CPU will receive that message and immediately send an ack.          *)
(* The value "requiredData" is the number of data items the CPU will have to    *)
(* fetch. The value "id" is a unique identifier for each GPU.              *)
(***************************************************************************)
Subscribe_GPU == 
    \E gpu_id \in 1..N_KGPU :
        LET
            gpu == KGpus[gpu_id]
            requiredData == gpu.missing_data - Len(gpu.memory)
            msg == [id |-> gpu_id, requiredData |-> requiredData]
            slot_exists == FindEmptySlot(gpu_id, LogicalSegments) > 0
        IN
            /\ gpu.state = "idle"
            /\ slot_exists
            /\ PushChannel' = Append(PushChannel, msg)
            /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "requesting"]
            /\ UNCHANGED <<LogicalSegments, Cpu, Streamlets>>


(***************************************************************************)
(* Action RcvACK_GPU defines a GPU receiving the ack form the cpu          *)
(* transitioning to "waiting" state.                                       *)
(***************************************************************************)                 
RcvACK_GPU ==
    \E gpu_id \in 1..N_KGPU :
        /\ KGpus[gpu_id].state = "requesting"
        /\ \E idx \in 1..LOGICAL_SEGMENT_SIZE : LogicalSegments[gpu_id][idx] # NULL  \* Check for at least one not NULL element
        /\ LET
            ack_idx == FindACKSlot(gpu_id, LogicalSegments)
          IN
            IF ack_idx > 0
            THEN 
                /\ LogicalSegments' = [LogicalSegments EXCEPT ![gpu_id][ack_idx] = NULL]
                /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "waiting"]
            ELSE 
                /\ LogicalSegments' = [LogicalSegments EXCEPT ![gpu_id] = [j \in 1..LOGICAL_SEGMENT_SIZE |-> NULL]]
                /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "idle"]
        /\ UNCHANGED <<Cpu, PushChannel, Streamlets>>

           
(***************************************************************************)
(* Action RcvData_GPU defines a GPU transitioning to "working" state.      *)
(* The GPU accessing the first element of its respective memory,           *)
(* storing it in its own memory, and removing it from the logical segment. *)
(***************************************************************************)
RcvData_GPU ==  /\ \E gpu_id \in 1..N_KGPU :
                    /\ KGpus[gpu_id].state = "waiting"
                    /\ \E idx \in 1..LOGICAL_SEGMENT_SIZE : LogicalSegments[gpu_id][idx] # NULL  \* Check for at least one not NULL element
                    /\ LET idx == FindDataSlot(gpu_id, LogicalSegments)
                       IN /\ idx > 0  \* Ensure there's a non-NULL data element present
                          /\ LET required_data == LogicalSegments[gpu_id][idx] IN
                             /\ KGpus' = [KGpus EXCEPT 
                                            ![gpu_id].memory = Append(KGpus[gpu_id].memory, required_data),
                                            ![gpu_id].state = "working"]                 
                             /\ LogicalSegments' = [LogicalSegments EXCEPT ![gpu_id][idx] = NULL]
                             /\ UNCHANGED <<Cpu, PushChannel, Streamlets>>

(***************************************************************************)
(* Action Waiting_GPU signals a GPU which is waiting for the data.         *)
(***************************************************************************)
Waiting_GPU ==  /\ \E gpu_id \in 1..N_KGPU :
                    /\ KGpus[gpu_id].state = "working"
                    /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "waiting"]
                    /\ UNCHANGED <<LogicalSegments, Cpu, PushChannel, Streamlets>>
                    
                    
Done_GPU == /\ \E gpu_id \in 1..N_KGPU :
                /\ KGpus[gpu_id].state = "waiting"
                /\ Len(KGpus[gpu_id].memory) = KGpus[gpu_id].missing_data
                /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "done"]
                /\ UNCHANGED <<LogicalSegments, Cpu, PushChannel, Streamlets>>
                
NewRequest_GPU ==
    \E gpu_id \in 1..N_KGPU :
        /\ KGpus[gpu_id].state = "done"
        /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "idle",
                                    ![gpu_id].missing_data = KGpus[gpu_id].missing_data + RandomElement(BoundedInt)]
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
            \/ Done_GPU
\*            \/ NewRequest_GPU

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

--------------------------------------------------------------------------
\* INVARIANTS
(***************************************************************************)
(* The GPU get the necessary data:                                         *)
(* This invariant ensures that for each GPU that is in the "done" state,   *)
(* the size of its memory is exactly equal to the required_data.           *)
(***************************************************************************)
MemorySizeEqualsRequiredData ==
    \A gpu_id \in 1..N_KGPU :
        IF KGpus[gpu_id].state = "done"
        THEN Len(KGpus[gpu_id].memory) = KGpus[gpu_id].missing_data
        ELSE TRUE

==========================================================================
