------------------------------ MODULE main ------------------------------
EXTENDS Integers, Sequences

VARIABLES Data,      \* The set of all possible data values.
          Cpu,       \* The record containing the state and the value.
          Buffer,    \* The buffer where the CPU will put the value.
          Gpu        \* The buffer where the GPU will store its values.


CONSTANTS NULL,      \* Placeholder for the initial empty value for the CPU
          StatesCpu  \* The set of all possible CPU states

(***************************************************************************)
(* Cpu is a record with a state in StatesCpu and a value in Data or NULL,  *)
(* Buffer is either empty or contains elements from Data,                  *)
(* Gpu is either empty or contains elements from Data.                     *)
(***************************************************************************)
TypeOK == /\ Cpu \in [state : StatesCpu, value : {NULL} \cup Data]
          /\ Buffer \in <<>> \cup Seq(Data)
          /\ Gpu \in <<>> \cup Seq(Data)
          /\ StatesCpu = {"idle", "fetching", "sending"}

vars == << Data, Cpu, Buffer, Gpu >>

(***************************************************************************)
(* Initially, Data is set to some initial values, StatesCpu contains the   *)
(* possible states, the CPU is in the "idle" state with no value,          *)
(* Buffer is empty, and Gpu is empty.                                      *)
(***************************************************************************)
Init == /\ Data = {1, 2, 3, 4, 5}
        /\ Cpu = [state |-> "idle", value |-> NULL]
        /\ Buffer = <<>>
        /\ Gpu = <<>>

(***************************************************************************)
(* Action Fetch defines the CPU transitioning from "idle" to "fetching"    *)
(* state and fetching a value from Data.                                   *)
(***************************************************************************)
FetchDataCPU == /\ Cpu.state = "idle"
                /\ Data # {}
                /\ LET d == CHOOSE x \in Data : TRUE IN
                   /\ Cpu' = [Cpu EXCEPT !.state = "fetching", !.value = d]
                   /\ UNCHANGED <<Buffer, Gpu, Data>>

(***************************************************************************)
(* Action SendDataCPU defines the CPU appending its value to the Buffer if *)
(* the CPU is in "fetching" state, and removes the value from the Data set.*)
(***************************************************************************)
SendDataCPU == /\ Cpu.state = "fetching"
               /\ Buffer' = Append(Buffer, Cpu.value)
               /\ Cpu' = [Cpu EXCEPT !.state = "sending", !.value = NULL]
               /\ Data' = Data \ {Cpu.value}
               /\ UNCHANGED Gpu
               
(***************************************************************************)
(* Action IdleCPU makes the CPU idle after sending the data.     *)
(* the CPU is in "fetching" state, and removes the value from the Data set.*)
(***************************************************************************)
IdleCPU ==     /\ Cpu.state = "sending"
               /\ Cpu' = [Cpu EXCEPT !.state = "idle"]
               /\ UNCHANGED <<Buffer, Gpu, Data>>

(***************************************************************************)
(* Action RcvDataGPU defines the GPU accessing the first element of the    *)
(* Buffer, storing it in its own buffer, and removing it from the Buffer.  *)
(***************************************************************************)
RcvDataGPU == /\ Buffer # <<>>
              /\ LET firstElem == Head(Buffer) IN
                   /\ Gpu' = Append(Gpu, firstElem)
                   /\ Buffer' = Tail(Buffer)
              /\ UNCHANGED <<Cpu, Data>>

(***************************************************************************)
(* Next defines the possible next actions in the system.                   *)
(***************************************************************************)
Next == FetchDataCPU \/ SendDataCPU \/ IdleCPU \/ RcvDataGPU

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
(* GPU.                                                                    *)
(***************************************************************************)
AllDataInGpu == <> (Buffer = <<>> /\ Gpu # <<>> /\ Data = {})

=============================================================================
