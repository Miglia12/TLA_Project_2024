------------------------------ MODULE main ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS NULL,                 \* Placeholder for the empty data_address
          ACK,                  \* Placeholder for the acknowledgement data_address
          N_KGPU,               \* Number of KGpus
          N_STREAMLETS,         \* Number of streamlets
          LOGICAL_SEGMENT_SIZE, \* Number of slots in each logical segment
          DataType,             \* Set of all possible data data_addresss
          BoundedInt            \* Set of Integers with a bound to avoid state space explosion

VARIABLES Cpu,              \* Record rapresenting the CPU
          Streamlets,       \* Collection of streamlets
          LogicalSegments,  \* Map of memory slots one for each GPU Kernel
          KGpus,            \* Record representing the GPU Kernels
          PushChannel       \* One-way message channel from GPU to CPU
          
-----------------------------------------------------------------------------
(***************************************************************************)
(*                              HELPER FUNCTIONS                           *)
(***************************************************************************)

(***************************************************************************)
(* FindEmptySlot:                                                          *)
(* Returns the index of the first occurrence of NULL or 0 if none is found.*)
(***************************************************************************)
FindEmptySlot(id, LogicalSegmentsMap) == 
    LET segment == LogicalSegments[id] IN
        IF \E idx \in 1..LOGICAL_SEGMENT_SIZE : segment[idx] = NULL
        THEN CHOOSE idx \in 1..LOGICAL_SEGMENT_SIZE : segment[idx] = NULL
        ELSE 0
        
(***************************************************************************)
(* FindDataSlot                                                            *)
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
-----------------------------------------------------------------------------
(***************************************************************************)
(*                              TYPE DEFINITIONS                           *)
(***************************************************************************)

(***************************************************************************)
(* CPU Type Definition:                                                    *)
(* - "idle": The CPU is not currently engaged in any operations.           *)
(* - "processing": The CPU processes a data request from a GPU.            *)
(* - "computing": The CPU is searching for the specified data within the   *)
(*   physical memory.                                                      *)
(* - "sending": The CPU prepares a streamlet to transmit the data to a GPU.*)
(* This structure defines the states of the CPU, the data_address being processed,*)
(* and the subscriptions (subs) which is a sequence of requests from GPUs. *)
(***************************************************************************)
CpuType == [ state : {"idle", "processing", "computing", "sending"},
             data_address : {NULL} \cup Int,
             subs : Seq([kgpu_id : 1..N_KGPU, required_data : Int]) ]

(***************************************************************************)
(* Logical Segments Type Definition:                                       *)
(* Each logical segment represents a portion of the Application Cache      *)
(* that is consumed by a single GPU kernel and filled by the StreamLet.    *)
(* Each GPU kernel has its own logical segment.                            *)
(***************************************************************************)
LogicalSegmentsType == [1..N_KGPU -> [1..LOGICAL_SEGMENT_SIZE -> DataType \cup {ACK, NULL}]]

(***************************************************************************)
(* GPU Kernel Type Definition:                                             *)
(* - "idle": The kernel is not currently engaged in any operations.        *)
(* - "requesting": The kernel has requested a certain amount of data,      *)
(*   specified as 'missing_data', from the CPU.                            *)
(* - "working": The kernel is processing the data from its logical segment.*)
(* - "waiting": The kernel awaits the arrival of data in its logical       *)
(*   segment before it can proceed with processing.                        *)
(* - "done": The kernel has obtained all the required data and completed   *)
(*   its processing tasks.                                                 *)
(***************************************************************************)
KGpuType == [ id : 1..N_KGPU,
              state : {"idle", "requesting", "working", "waiting", "done"},
              missing_data : Int,
              memory : Seq(DataType) ]

(***************************************************************************)
(* Collection of KGpus Type Definition:                                    *)
(* This defines a mapping from each GPU ID (from 1 to N_KGPU) to an        *)
(* instance of KGpuType, representing each GPU kernel in the system.       *)
(***************************************************************************)
KGpusType == [1..N_KGPU -> KGpuType]

(***************************************************************************)
(* PushChannel Type Definition:                                            *)
(* This defines a sequence representing the one-way message channel from   *)
(* GPUs to the CPU. Each element in the sequence is a record specifying    *)
(* the GPU ID and the amount of data required by that GPU.                 *)
(***************************************************************************)
PushChannelType == Seq([id : 1..N_KGPU, requiredData : Int])

(***************************************************************************)
(* Streamlet Type Definition:                                              *)
(* A streamlet is responsible for transferring data to the logical segment *)
(* of a GPU kernel. It is initialized by the CPU and iterates over physical *)
(* memory addresses until all data is transferred.                          *)
(*                                                                          *)
(* - "start_address": The initial memory address.                           *)
(* - "stop_address": The memory address where the streamlet's task ends.    *)
(* - "kgpu_id": Identifier for the associated GPU kernel, ranging from 1 to *)
(*   N_KGPU.                                                               *)
(* - "current_address": Tracks the current memory address being accessed   *)
(*   within the streamlet to monitor progress in data processing.           *)
(***************************************************************************)
StreamletType == [ start_address : Int,
                   stop_address : Int,
                   kgpu_id : 1..N_KGPU,
                   current_address : Int ]

(***************************************************************************)
(* Collection of Streamlets Type Definition:                               *)
(* This type represents a mapping from each streamlet identifier (from 1   *)
(* to N_STREAMLETS) to an instance of StreamletType.                       *)
(***************************************************************************)
StreamletsType == [1..N_STREAMLETS -> StreamletType]

(***************************************************************************)
(*                                  TypeOK                                 *)
(***************************************************************************)
TypeOK == /\ NULL \notin Int
          /\ ACK \notin Int
          /\ Cpu \in CpuType
          /\ Streamlets \in StreamletsType
          /\ LogicalSegments \in LogicalSegmentsType
          /\ KGpus \in KGpusType
          /\ PushChannel \in PushChannelType

vars == << Cpu, Streamlets, LogicalSegments, KGpus, PushChannel>>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            ACTIONS DEFINITIONS                          *)
(***************************************************************************)

(***************************************************************************)
(* Initial State of the System:                                            *)
(* Each component is initialized as follows:                               *)
(* - Cpu: Set to idle state, with no current data_address or subscriptions.*)
(* - Streamlets: Each streamlet is initialized with starting and stopping  *)
(*   addresses set to zero.                                                *)
(* - LogicalSegments: Each GPU's memory segment is initialized to NULL,    *)
(*   indicating no data is currently stored.                               *)
(* - KGpus: Each GPU starts in an idle state with a random element from    *)
(*   BoundedInt as the initial missing data and no data in memory.         *)
(* - PushChannel: Initialized as empty, indicating no pending messages.    *)
(***************************************************************************)
Init == 
    /\ Cpu = [ state |-> "idle", 
               data_address |-> NULL, 
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
(* Action: ReceiveMsg_CPU                                                  *)
(* This action describes how the CPU handles receiving a message from the  *)
(* PushChannel. The CPU processes the first                                *)
(* message in the channel, marks a slot in the logical segment of the      *)
(* corresponding GPU with an ACK, and updates its state and subscriptions. *)
(* After processing, the message is removed from the PushChannel.          *)
(***************************************************************************)
ReceiveMsg_CPU ==
    /\ Cpu.state = "idle"
    /\ PushChannel # <<>>
    /\ LET
        msg == Head(PushChannel)
        idx == FindEmptySlot(msg.id, LogicalSegments)
       IN
        /\ idx > 0 \* A precondition to enable this action is that there must be an empty slot in the LogicalSegment.
        /\ Cpu' = [Cpu EXCEPT 
                    !.state = "processing", 
                    !.subs = Append(Cpu.subs, [kgpu_id |-> msg.id, required_data |-> msg.requiredData])]
        /\ LogicalSegments' = [LogicalSegments EXCEPT ![msg.id][idx] = ACK]
        /\ PushChannel' = Tail(PushChannel)
        /\ UNCHANGED <<KGpus, Streamlets>>

(***************************************************************************)
(* Action: ComputeDataLocation_CPU                                         *)
(* This action is triggered when the CPU is idle, has no current data_address,*)
(* and has pending subscriptions. It attempts to find a data location for  *)
(* processing:                                                             *)
(* - If there is data to provide to a GPU kernel, the CPU transitions to the *)
(*   "computing" state and assigns a randomly chosen address as the data_address. *)
(* - If no data is needed (required_data = 0), it removes the top          *)
(*   subscription and remains unchanged.                                   *)
(***************************************************************************)
ComputeDataLocation_CPU == 
    /\ Cpu.state = "idle"
    /\ Cpu.subs # <<>>
    /\ Cpu.data_address = NULL
    /\ LET
        sub == Head(Cpu.subs)
        address == RandomElement(BoundedInt)
       IN
        IF sub.required_data # 0 THEN
            /\ Cpu' = [Cpu EXCEPT !.state = "computing", !.data_address = address]
            /\ UNCHANGED <<LogicalSegments, KGpus, PushChannel, Streamlets>>
        ELSE
            /\ Cpu' = [Cpu EXCEPT !.subs = Tail(Cpu.subs)]
            /\ UNCHANGED <<KGpus, PushChannel, LogicalSegments, Cpu.state, Cpu.data_address, Streamlets>>

(***************************************************************************)
(* StartStream_CPU Action:                                                 *)
(* This action initializes the data streaming process for a Streamlet when *)
(* the CPU is idle and holds a valid data_address. It updates              *)
(* the CPU state to "sending" and sets up the streamlet with new data      *)
(* boundaries (start and stop addresses) based on the CPU's current data_address  *)
(* and required data from the subscriptions list. The CPU's data_address is then  *)
(* cleared, and it moves to the next subscription.                         *)
(***************************************************************************)
StartStream_CPU ==
    /\ Cpu.state = "idle"
    /\ Cpu.data_address # NULL
    /\ LET sub == Head(Cpu.subs)
          new_start_address == Cpu.data_address
          new_stop_address == Cpu.data_address + sub.required_data
          new_current_address == Cpu.data_address
          new_kgpu_id == sub.kgpu_id
       IN
        /\ \E streamlet \in DOMAIN Streamlets :
               /\ Streamlets[streamlet].current_address >= Streamlets[streamlet].stop_address
               /\ Streamlets' = [Streamlets EXCEPT 
                                   ![streamlet].start_address = new_start_address,
                                   ![streamlet].stop_address = new_stop_address,
                                   ![streamlet].kgpu_id = new_kgpu_id,
                                   ![streamlet].current_address = new_current_address]
        /\ Cpu' = [Cpu EXCEPT 
                    !.state = "sending", 
                    !.data_address = NULL,
                    !.subs = Tail(Cpu.subs)]
        /\ UNCHANGED <<KGpus, PushChannel, LogicalSegments>>

(***************************************************************************)
(* Idle_CPU Action:                                                        *)
(* This action transitions the CPU from an active state (computing,        *)
(* sending, or processing) back to an idle state. This reflects a          *)
(* completion of tasks or a pause in activities                            *)
(***************************************************************************)
Idle_CPU == 
    /\ Cpu.state \in {"computing", "sending", "processing"}
    /\ Cpu' = [Cpu EXCEPT !.state = "idle"]                  
    /\ UNCHANGED <<LogicalSegments, KGpus, PushChannel, Streamlets>>
               
(***************************************************************************)
(* Stream Action:                                                          *)
(* This action represents the process of streaming data from streamlets to *)
(* their respective GPU's logical segments. It operates under the          *)
(* condition that the current address of a streamlet has not yet reached   *)
(* its stop address, indicating ongoing data transmission.                 *)
(* - Finds an empty slot in the GPU's logical segment.                     *)
(* - Chooses a piece of data from the DataType set to stream.              *)
(* - Updates the logical segment with the new data and increments the      *)
(*   streamlet's current address.                                          *)
(***************************************************************************)
Stream ==
    \E s \in DOMAIN Streamlets :
        /\ Streamlets[s].current_address < Streamlets[s].stop_address 
        /\ LET
            idx == FindEmptySlot(Streamlets[s].kgpu_id, LogicalSegments) 
            data == CHOOSE x \in DataType : TRUE
           IN
            /\ idx > 0  \* Confirm that an empty slot exists
            /\ LogicalSegments' = [LogicalSegments EXCEPT ![Streamlets[s].kgpu_id][idx] = data]
            /\ Streamlets' = [Streamlets EXCEPT ![s].current_address = Streamlets[s].current_address + 1]
            /\ UNCHANGED <<Cpu, KGpus, PushChannel>>

(***************************************************************************)
(* SomeGpuRequestsData Action:                                             *)
(* This action models a GPU in the system transitioning from an idle state *)
(* to requesting data. A GPU, identified by gpu_id, calculates the amount  *)
(* of data it still requires (missing_data minus the length of its memory) *)
(* and sends a request to the CPU via the PushChannel.                     *)
(***************************************************************************)
SomeGpuRequestsData == 
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
(* Action: SomeGpuReceivesACK                                               *)
(* This action describes the transition of a GPU from the "requesting"     *)
(* state to "waiting" upon successfully receiving an ACK. The action       *)
(* checks if there is an ACK in any GPU's logical segment and if found,    *)
(* clears it and updates the GPU's state. This signifies the GPU has       *)
(* received the necessary acknowledgment to proceed to the next step.      *)
(***************************************************************************)              
SomeGpuReceivesACK ==
    \E gpu_id \in 1..N_KGPU :
        /\ KGpus[gpu_id].state = "requesting"
        /\ LET ack_idx == FindACKSlot(gpu_id, LogicalSegments)
           IN
            /\ ack_idx > 0   \* Precondition: ACK must be found
            /\ LogicalSegments' = [LogicalSegments EXCEPT ![gpu_id][ack_idx] = NULL]
            /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "waiting"]
        /\ UNCHANGED <<Cpu, PushChannel, Streamlets>>


           
(***************************************************************************)
(* Action: SomeGpuReceivesData                                             *)
(* This action describes the transition of a GPU from waiting to working   *)
(* state when it successfully receives required data. For any GPU in a     *)
(* waiting state, this action checks for a non-empty data slot in the      *)
(* logical segments. If found, the data is moved into the GPU's memory,    *)
(* the data slot is cleared.                                               *)
(***************************************************************************)
SomeGpuReceivesData ==
    \E gpu_id \in 1..N_KGPU :
        /\ KGpus[gpu_id].state = "waiting"
        /\ LET data_idx == FindDataSlot(gpu_id, LogicalSegments)
           IN
            /\ data_idx > 0  \* Ensure there's a valid data slot
            /\ LET required_data == LogicalSegments[gpu_id][data_idx]
               IN
                /\ KGpus' = [KGpus EXCEPT 
                               ![gpu_id].memory = Append(@, required_data),
                               ![gpu_id].state = "working"]
                /\ LogicalSegments' = [LogicalSegments EXCEPT ![gpu_id][data_idx] = NULL]
                /\ UNCHANGED <<Cpu, PushChannel, Streamlets>>


(***************************************************************************)
(* SomeGpuWaits Action:                                                    *)
(* This action transitions a GPU from a "working" state to a "waiting"     *)
(* state. It applies to any GPU currently in the "working" state,          *)
(* indicating that the GPU has completed its current tasks and is now      *)
(* awaiting further data.                                                  *)
(***************************************************************************)
SomeGpuWaits ==
    \E gpu_id \in 1..N_KGPU :
        /\ KGpus[gpu_id].state = "working"
        /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "waiting"]
        /\ UNCHANGED <<LogicalSegments, Cpu, PushChannel, Streamlets>>
     
(***************************************************************************)
(* Action: SomeGpuFinished                                                 *)
(* This action transitions a GPU from the "waiting" state to the "done"    *)
(* state if it has successfully collected all its required data.           *)
(***************************************************************************)
SomeGpuFinished ==
    \E gpu_id \in 1..N_KGPU :
        /\ KGpus[gpu_id].state = "waiting"
        /\ Len(KGpus[gpu_id].memory) = KGpus[gpu_id].missing_data
        /\ KGpus' = [KGpus EXCEPT ![gpu_id].state = "done"]
        /\ UNCHANGED <<LogicalSegments, Cpu, PushChannel, Streamlets>>



(***************************************************************************)
(* Next defines the possible next actions in the system.                   *)
(***************************************************************************)
Next ==     \/ ReceiveMsg_CPU 
            \/ ComputeDataLocation_CPU 
            \/ StartStream_CPU 
            \/ Idle_CPU 
            \/ Stream
            \/ SomeGpuRequestsData 
            \/ SomeGpuReceivesACK
            \/ SomeGpuReceivesData 
            \/ SomeGpuWaits
            \/ SomeGpuFinished

(***************************************************************************)
(* The overall specification, starts with Init and requires that           *)
(* Next is always enabled.                                                 *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* FairSpec is Spec with the additional requirement that it keeps taking   *)
(* steps.                                                                  *)
(***************************************************************************)
FairSpec == Spec /\ WF_vars(Next)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                              SYSTEM PROPERTIES                          *)
(***************************************************************************)

(***************************************************************************)
(* Termination Conditions and Liveness Property:                           *)
(* - AllGPUsDone: Checks that every GPU in the system has completed its    *)
(*   tasks and is in the "done" state.                                     *)
(* - CPUIdle: Verifies that the CPU is in the "idle" state, not performing *)
(*   any current operations.                                               *)
(* - TerminationCondition: The overall system reaches termination when    *)
(*   all GPUs are done and the CPU is idle, indicating no ongoing         *)
(*   activities or processing.                                             *)
(* - EventuallyTerminate: A liveness property asserting that the system    *)
(*   is guaranteed to eventually reach the termination condition,         *)
(*   ensuring that the system does not remain indefinitely active.         *)
(***************************************************************************)
AllGPUsDone == \A gpu_id \in DOMAIN KGpus : KGpus[gpu_id].state = "done"
CPUIdle == Cpu.state = "idle"

TerminationCondition == AllGPUsDone /\ CPUIdle

EventuallyTerminate == <>TerminationCondition

(***************************************************************************)
(* Invariant - GPUs Achieve Necessary Data Load:                           *)
(* Ensures that for each GPU that reaches the "done" state, the amount of  *)
(* data stored in its memory matches the initially required data amount    *)
(* specified by 'missing_data'.                                            *)
(***************************************************************************)
MemorySizeEqualsRequiredData ==
    \A gpu_id \in 1..N_KGPU :
        KGpus[gpu_id].state = "done" => Len(KGpus[gpu_id].memory) = KGpus[gpu_id].missing_data
        
(***************************************************************************)
(* Invariant - Complete Data Utilization by GPUs:                          *)
(* Ensures that when a GPU kernel reaches the "done" state,                *)
(* all data originally required has been successfully processed and stored *)
(* in its memory, and all associated logical segments have been cleared.   *)
(***************************************************************************)     
CorrectMemoryUtilization == 
    \A id \in 1..N_KGPU :
        KGpus[id].state = "done" =>
            (Len(KGpus[id].memory) = KGpus[id].missing_data /\
             \A idx \in 1..LOGICAL_SEGMENT_SIZE : LogicalSegments[id][idx] = NULL)
             
(***************************************************************************)
(* Invariant - Correct Streamlet Assignment:                               *)
(* This invariant ensures that each streamlet is assigned to only one GPU  *)
(* at any time and prevents any two streamlets from overlapping in their   *)
(* service to the same GPU unless the previous tasks are completed. This   *)
(* guarantees that there is no conflict or data corruption during GPU data *)
(* processing.                                                             *)
(***************************************************************************)  
CorrectStreamletAssignment ==
    \A s \in 1..N_STREAMLETS :
        \A t \in 1..N_STREAMLETS \ {s} :
            (Streamlets[s].kgpu_id # Streamlets[t].kgpu_id)
            \/ (Streamlets[s].current_address >= Streamlets[t].stop_address)
            \/ (Streamlets[t].current_address >= Streamlets[s].stop_address)

==========================================================================
