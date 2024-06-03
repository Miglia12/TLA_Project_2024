------------------------------ MODULE main ------------------------------
EXTENDS Integers, Sequences

VARIABLES Data,      \* The set of all possible data values.
          Cpu,       \* The record containing the state and the value.
          Buffer,    \* The buffer where the CPU will put the value.
          GpuBuffer, \* The buffer where the GPU will store its values.
          Gpu,       \* The record representing the GPU entity.
          MsgChannel \* One way message channel from GPU to CPU.

CONSTANTS NULL,      \* Placeholder for the initial empty value for the CPU
          StatesCpu, \* The set of all possible CPU states
          StatesGpu  \* The set of all possible GPU states

-------------------------------------------------------------------------------------------- 
(***************************************************************************)
(* Helper function to check if an element is not in a sequence.            *)
(***************************************************************************)
NotInSeq(elem, seq) == \A i \in 1..Len(seq) : elem # seq[i]

(***************************************************************************)
(* Helper function to find the index of an element in a sequence.          *)
(***************************************************************************)
IndexOf(elem, seq) == 
    IF \E i \in 1..Len(seq) : seq[i] = elem THEN
        CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE
        Len(seq) + 1  \* If elem is not found, return an index outside the range

(***************************************************************************)
(* Helper function to remove an element from a sequence.                   *)
(***************************************************************************)
RemoveFromSeq(elem, seq) == 
    \* Create a new sequence by including elements from seq except the one equal to elem
    [i \in 1..(Len(seq) - 1) |-> 
        IF i < IndexOf(elem, seq) THEN seq[i]
        ELSE seq[i + 1]
    ]
-------------------------------------------------------------------------------------------- 

(***************************************************************************)
(* Cpu is a record with a state in StatesCpu, a value in Data or NULL,     *)
(* a remaining count which is an integer, and a list of subscribed GPU IDs.*)
(* Buffer is a sequence of elements from Data or is empty.                 *)
(* GpuBuffer is a sequence of elements from Data or is empty.              *)
(* Gpu is a record with an ID, a state in StatesGpu, and a counter for     *)
(* the amount of data needed.                                              *)
(* MsgChannel is a sequence of messages from GPU to CPU or is empty.       *)
(***************************************************************************)
TypeOK == /\ Cpu \in [state : StatesCpu, value : {NULL} \cup Data, remaining : Int, subscribed : Seq(Int)]
          /\ Buffer \in <<>> \cup Seq(Data)
          /\ GpuBuffer \in <<>> \cup Seq(Data)
          /\ Gpu \in [id : Int, state : StatesGpu, missing_data : Int]
          /\ MsgChannel \in <<>> \cup Seq([id : Int, numData : Int])
          /\ StatesCpu = {"processing", "fetching", "sending", "idle"}
          /\ StatesGpu = {"idle", "requesting", "working"}

vars == << Data, Cpu, Buffer, GpuBuffer, Gpu, MsgChannel >>

(***************************************************************************)
(* Initially, Data is set to some initial values, StatesCpu contains the   *)
(* possible states, the CPU is in the "idle" state with no value and an    *)
(* empty list of subscribed GPUs, Buffer is empty, GpuBuffer is empty,     *)
(* Gpu is idle with ID 1 and needs 3 data items, and MsgChannel is empty.  *)
(***************************************************************************)
Init == /\ Data = {1, 2, 3}
        /\ Cpu = [state |-> "idle", value |-> NULL, remaining |-> 0, subscribed |-> <<>>]
        /\ Buffer = <<>>
        /\ GpuBuffer = <<>>
        /\ Gpu = [id |-> 1, state |-> "idle", missing_data |-> 3]
        /\ MsgChannel = <<>>

(***************************************************************************)
(* Action ReceiveMsg_CPU defines the CPU adding a new GPU to which it will *)
(* have to provide data to.                                                *)
(* The GPU can subscribe to get data at any given point, so the CPU keeps  *)
(* a record of the subscribed GPU to avoid restarting the communication and*)
(* blocking other GPUs. Upon receiving a message, if the ID of the GPU is  *)
(* already in the list it will get discarded otherwise it will be added and*)
(* the CPU will start providing data to the GPU.                           *)
(***************************************************************************)
ReceiveMsg_CPU == /\ Cpu.state = "idle"
                  /\ MsgChannel # <<>>
                  /\ Data # {} \* TODO remove check eventually
                  /\ LET msg == Head(MsgChannel) IN
                     IF (NotInSeq(msg.id, Cpu.subscribed) /\ msg.numData > 0) THEN
                        /\ Cpu' = [Cpu EXCEPT !.state = "processing", !.remaining = msg.numData, !.subscribed = Append(Cpu.subscribed, msg.id)]
                        /\ MsgChannel' = Tail(MsgChannel)
                     ELSE
                        IF msg.numData = 0 THEN
                            /\ RemoveFromSeq(msg.id, Cpu.subscribed)
                        ELSE
                            /\ Cpu' = [Cpu EXCEPT !.state = "processing"]
                            /\ MsgChannel' = Tail(MsgChannel)
                  /\ UNCHANGED <<Buffer, GpuBuffer, Data, Gpu>>

(***************************************************************************)
(* Action FetchData_CPU defines the CPU transitioning to the               *)
(* state "fetching". Until the subscribed GPU needs data (Cpu.remaining)   *)
(* the CPU will provide it with data.                                      *)
(***************************************************************************)
FetchData_CPU ==    /\ Cpu.state = "idle"
                    /\ Cpu.remaining > 0
                    /\ Cpu.value = NULL
                    /\ Data # {} \* TODO remove check eventually
                    /\ LET d == CHOOSE x \in Data : TRUE IN
                        /\ Cpu' = [Cpu EXCEPT !.state = "fetching", !.value = d]
                    /\ UNCHANGED <<Buffer, Gpu, GpuBuffer, Data, MsgChannel>>

(***************************************************************************)
(* Action SendData_CPU defines the CPU transitioning to the state "sending".*)
(* The CPU will append the data it fetched in the buffer so that the GPU   *)
(* can fetch it.                                                           *)
(***************************************************************************)
SendData_CPU == /\ Cpu.state = "idle"
                /\ Cpu.value # NULL
                /\ Data # {} \* TODO remove check eventually
                /\ Buffer' = Append(Buffer, Cpu.value)
                /\ Cpu' = [Cpu EXCEPT !.state = "sending", !.value = NULL, !.remaining = @ - 1]
                /\ Data' = Data \ {Cpu.value}
                /\ UNCHANGED <<Gpu, GpuBuffer, MsgChannel>>

(***************************************************************************)
(* Action Idle_CPU makes the CPU idle after every action.                  *)
(***************************************************************************)
Idle_CPU ==    /\ Cpu.state \in {"fetching", "sending", "processing"}
               /\ Cpu' = [Cpu EXCEPT !.state = "idle"]
               /\ UNCHANGED <<Buffer, Gpu, GpuBuffer, Data, MsgChannel>>

(***************************************************************************)
(* Action Subscribe_GPU defines the GPU sending a message to the CPU and   *)
(* transitioning to "requesting" state.                                    *)
(* The CPU will receive that message and start fetching data.              *)
(* The value "numData" is the number of data items the CPU will have to    *)
(* fetch. The value "id" is a unique identifier for each GPU.              *)
(***************************************************************************)
\* TODO without cheking for data the GPU can request to be subscribed for ever
\*      this makes the specification stutter in a loop. Find a way to avoid this.
Subscribe_GPU == /\ Gpu.state = "idle"
                 /\ Buffer = <<>>
                 /\ Data # {} \* TODO remove check eventually
                 /\ LET msg == [id |-> Gpu.id, numData |-> Gpu.missing_data] IN
                      /\ MsgChannel' = Append(MsgChannel, msg)
                      /\ Gpu' = [Gpu EXCEPT !.state = "requesting"]
                 /\ UNCHANGED <<Buffer, Cpu, GpuBuffer, Data>>

(***************************************************************************)
(* Action RcvData_GPU defines the GPU transitioning to "working" state.    *)
(* The GPU accessing the first element of the Buffer,                      *)
(* storing it in its own buffer, and removing it from the Buffer.          *)
(***************************************************************************)
RcvData_GPU == /\ Gpu.state = "idle"
               /\ Buffer # <<>>
               /\ LET firstElem == Head(Buffer) IN
                    /\ GpuBuffer' = Append(GpuBuffer, firstElem)
                    /\ Buffer' = Tail(Buffer)
                    /\ Gpu' = [Gpu EXCEPT !.state = "working", !.missing_data = @ - 1]
               /\ UNCHANGED <<Cpu, Data, MsgChannel>>

(***************************************************************************)
(* Action Idle_GPU makes the GPU idle after every action.                  *)
(***************************************************************************)
Idle_GPU == /\ Gpu.state \in {"requesting", "working"}
           /\ Gpu' = [Gpu EXCEPT !.state = "idle"]
           /\ UNCHANGED <<Buffer, Cpu, GpuBuffer, Data, MsgChannel>>

(***************************************************************************)
(* Next defines the possible next actions in the system.                   *)
(***************************************************************************)
Next ==     \/ ReceiveMsg_CPU 
            \/ FetchData_CPU 
            \/ SendData_CPU 
            \/ Idle_CPU 
            \/ Subscribe_GPU 
            \/ RcvData_GPU 
            \/ Idle_GPU

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
(* GPU buffer.                                                             *)
(***************************************************************************)
AllDataInGpu == <> (Buffer = <<>> /\ GpuBuffer # <<>> /\ Data = {})

==========================================================================

