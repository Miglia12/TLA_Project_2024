------------------------------ MODULE main ------------------------------
EXTENDS Integers, Sequences

VARIABLES Data,      \* The set of all possible data values.
          StatesCpu, \* The set of all possible CPU states.
          Cpu,       \* The record containing the state and the value.
          Buffer,    \* The buffer where the CPU will put the value.
          Gpu        \* The buffer where the GPU will store its values.

(***************************************************************************)
(* Define a placeholder for the initial empty value for the CPU.           *)
(***************************************************************************)
CONSTANT NULL

(***************************************************************************)
(* Cpu is a record with a state in StatesCpu and a value in Data or NULL,  *)
(* Buffer is either empty or contains elements from Data,                  *)
(* Gpu is either empty or contains elements from Data.                     *)
(***************************************************************************)
TypeOK == /\ Cpu \in [state : StatesCpu, value : {NULL} \cup Data]
          /\ Buffer \in <<>> \cup Seq(Data)
          /\ Gpu \in <<>> \cup Seq(Data)
          /\ StatesCpu = {"idle", "fetching", "sending"}

vars == << Data, StatesCpu, Cpu, Buffer, Gpu >>

(***************************************************************************)
(* Initially, Data is set to some initial values, StatesCpu contains the   *)
(* possible states, the CPU is in the "idle" state with no value,          *)
(* Buffer is empty, and Gpu is empty.                                      *)
(***************************************************************************)
Init == /\ Data = {1, 2, 3, 4, 5}
        /\ StatesCpu = {"idle", "fetching", "sending"}
        /\ Cpu = [state |-> "idle", value |-> NULL]
        /\ Buffer = <<>>
        /\ Gpu = <<>>

(***************************************************************************)
(* Action Fetch defines the CPU transitioning from "idle" to "fetching"    *)
(* state and fetching a value from Data.                                   *)
(***************************************************************************)
Fetch == /\ Cpu.state = "idle"
         /\ Data # {}
         /\ LET d == CHOOSE x \in Data : TRUE IN
            Cpu' = [Cpu EXCEPT !.state = "fetching", !.value = d]
         /\ UNCHANGED <<Buffer, Gpu, Data, StatesCpu>>

(***************************************************************************)
(* Action Put defines the CPU putting its value into the Buffer if the     *)
(* Buffer is empty and CPU is in "fetching" state, and removes the value   *)
(* from the Data set.                                                      *)
(***************************************************************************)
Put == /\ Cpu.state = "fetching"
       /\ Buffer = <<>>
       /\ Buffer' = <<Cpu.value>>
       /\ Cpu' = [Cpu EXCEPT !.state = "idle", !.value = NULL]
       /\ Data' = Data \ {Cpu.value}
       /\ UNCHANGED Gpu
       /\ UNCHANGED StatesCpu

(***************************************************************************)
(* Action GpuAccess defines the GPU accessing the Buffer and storing the   *)
(* value in its own buffer if the GPU buffer is empty and the CPU buffer   *)
(* is not empty.                                                           *)
(***************************************************************************)
GpuAccess == /\ Buffer # <<>>
             /\ Gpu = <<>>
             /\ Gpu' = Buffer
             /\ Buffer' = <<>>
             /\ UNCHANGED <<Cpu, Data, StatesCpu>>

(***************************************************************************)
(* Next defines the possible next actions in the system.                   *)
(***************************************************************************)
Next == Fetch \/ Put \/ GpuAccess

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
