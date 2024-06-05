------------------------------ MODULE main ------------------------------
EXTENDS Integers, Sequences

VARIABLES Data,      \* The set of all possible data values.
          Cpu,       \* The record containing the state and the value.
          Buffer,    \* The buffer where the CPU will put the value.
          Gpu,       \* The record representing the GPU entity.
          PushChannel \* One way message channel from GPU to CPU.

CONSTANTS NULL,      \* Placeholder for the empty value
          ACK,      \* Placeholder for the ack value
          StatesCpu, \* The set of all possible CPU states
          StatesGpu, \* The set of all possible GPU states
          MAX_INT_VALUE \* The ceiling for all data values

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
(* Cpu is a record with a state in StatesCpu, a value in Data or NULL,     *)
(* a remaining count which is an integer, and a list of subscribed GPU IDs.*)
(* Buffer is a sequence of elements from Data or is empty.                 *)
(* Gpu is a record with an ID, a state in StatesGpu, a counter for         *)
(* the amount of data needed, and a buffer to store its values.            *)
(* PushChannel is a sequence of messages from GPU to CPU or is empty.       *)
(***************************************************************************)
TypeOK == /\ Cpu \in [state : StatesCpu, value : {NULL} \cup Data, remaining : Int, subscribed : Seq(Int)]
          /\ Buffer \in <<>> \cup Seq(Data)
          /\ Gpu \in [id : Int, state : StatesGpu, missing_data : Int, buffer : {ACK} \cup Seq(Data)]
          /\ PushChannel \in <<>> \cup Seq([id : Int, numData : Int])
          /\ StatesCpu = {"processing", "fetching", "sending", "idle"}
          /\ StatesGpu = {"idle", "requesting", "working", "waiting"}

vars == << Data, Cpu, Buffer, Gpu, PushChannel >>

(***************************************************************************)
(* Initially, Data is a set of natural numbers up to MAX_INT_VALUE,       *)
(* StatesCpu contains the possible states, the CPU is in the "idle" state  *)
(* with no value and an empty list of subscribed GPUs, Buffer is empty,    *)
(* Gpu is idle with ID 1 and needs a random number of data items within    *)
(* 1 to MAX_INT_VALUE, and an empty buffer, and PushChannel is empty.      *)
(***************************************************************************)
Init == /\ Data = ACK + 1..MAX_INT_VALUE
        /\ Cpu = [state |-> "idle", value |-> NULL, remaining |-> 0, subscribed |-> <<>>]
        /\ Buffer = <<>>
        /\ Gpu = [id |-> 1, state |-> "idle", missing_data |-> CHOOSE x \in 3..MAX_INT_VALUE : TRUE, buffer |-> <<>>]
        /\ PushChannel = <<>>

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
                  /\ PushChannel # <<>>
                  /\ LET msg == Head(PushChannel) IN
                    /\ Cpu' = [Cpu EXCEPT !.state = "processing", !.remaining = msg.numData, !.subscribed = Append(Cpu.subscribed, msg.id)]
                    /\ PushChannel' = Tail(PushChannel)
                    /\ Buffer' = Append(Buffer, ACK)
                  /\ UNCHANGED <<Gpu, Data>>

(***************************************************************************)
(* Action FetchData_CPU defines the CPU transitioning to the               *)
(* state "fetching". Until the subscribed GPU needs data (Cpu.remaining)   *)
(* the CPU will provide it with data.                                      *)
(***************************************************************************)
FetchData_CPU ==    /\ Cpu.state = "idle"
                    /\ Cpu.remaining > 0
                    /\ Cpu.value = NULL
                    /\ LET d == CHOOSE x \in Data : TRUE IN
                        /\ Cpu' = [Cpu EXCEPT !.state = "fetching", !.value = d]
                    /\ UNCHANGED <<Buffer, Gpu, Data, PushChannel>>

(***************************************************************************)
(* Action SendData_CPU defines the CPU transitioning to the state "sending".*)
(* The CPU will append the data it fetched in the buffer so that the GPU   *)
(* can fetch it.                                                           *)
(***************************************************************************)
SendData_CPU == /\ Cpu.state = "idle"
                /\ Cpu.value # NULL
                /\ Buffer' = Append(Buffer, Cpu.value)
                /\ Cpu' = [Cpu EXCEPT !.state = "sending", !.value = NULL, !.remaining = @ - 1]
                /\ UNCHANGED <<Gpu, PushChannel, Data>>

(***************************************************************************)
(* Action Idle_CPU makes the CPU idle after every action.                  *)
(***************************************************************************)
Idle_CPU ==    /\ Cpu.state \in {"fetching", "sending", "processing"}
               /\ Cpu' = [Cpu EXCEPT !.state = "idle"]
               /\ UNCHANGED <<Buffer, Gpu, Data, PushChannel>>

(***************************************************************************)
(* Action Subscribe_GPU defines the GPU sending a message to the CPU and   *)
(* transitioning to "requesting" state.                                    *)
(* The CPU will receive that message and start fetching data.              *)
(* The value "numData" is the number of data items the CPU will have to    *)
(* fetch. The value "id" is a unique identifier for each GPU.              *)
(***************************************************************************)
\* Assuming that the request will not be lost.
Subscribe_GPU == /\ Gpu.state = "idle"
                 /\ Buffer = <<>>       
                 /\ LET msg == [id |-> Gpu.id, numData |-> Gpu.missing_data] IN
                      /\ PushChannel' = Append(PushChannel, msg)
                      /\ Gpu' = [Gpu EXCEPT !.state = "waiting"]
                 /\ UNCHANGED <<Buffer, Cpu, Data>>

(***************************************************************************)
(* Action RcvData_GPU defines the GPU transitioning to "working" state.    *)
(* The GPU accessing the first element of the Buffer,                      *)
(* storing it in its own buffer, and removing it from the Buffer.          *)
(***************************************************************************)
\* TODO: Make a choice about the Kernel to have more than 2 states
RcvData_GPU ==  /\ Gpu.state = "waiting"
                /\ Buffer # <<>>
                /\ LET required_data == Head(Buffer) IN
                    IF (required_data > ACK) THEN
                        /\ Gpu' = [Gpu EXCEPT !.buffer = Append(Gpu.buffer, required_data), !.state = "working", !.missing_data = @ - 1]                 
                    ELSE 
                        /\ Gpu' = [Gpu EXCEPT !.state = "working"]
                /\ Buffer' = Tail(Buffer)
                /\ UNCHANGED <<Cpu, Data, PushChannel>>

(***************************************************************************)
(* Action Waiting_GPU signals a GPU which is waiting for the data.         *)
(***************************************************************************)
Waiting_GPU ==  /\ Gpu.state \in {"working"}
                /\ Gpu' = [Gpu EXCEPT !.state = "waiting"]
                /\ UNCHANGED <<Buffer, Cpu, Data, PushChannel>>

(***************************************************************************)
(* Next defines the possible next actions in the system.                   *)
(***************************************************************************)
Next ==     \/ ReceiveMsg_CPU 
            \/ FetchData_CPU 
            \/ SendData_CPU 
            \/ Idle_CPU 
            \/ Subscribe_GPU 
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
(* GPU buffer.                                                             *)
(***************************************************************************)
AllDataInGpu == <> (Buffer = <<>> /\ Gpu.buffer # <<>>)

==========================================================================
