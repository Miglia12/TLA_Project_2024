------------------------------ MODULE main --------------------------------
EXTENDS Integers, Sequences

CONSTANT Data  \* The set of all possible data values.

VARIABLES CpuBroker,   \* The last <<value, bit>> record cpu_broker decided to send.
          GpuKernel    \* The last <<value, bit>> record gpu_kernel received.
          
(***************************************************************************)
(* Type correctness means that CpuBroker and GpuKernel are records         *)
(* [value |-> d, bit |-> i] where d \in Data and i \in {0, 1}.             *)
(***************************************************************************)
TypeOK == /\ CpuBroker \in [value: Data, bit: {0, 1}]
          /\ GpuKernel \in [value: Data, bit: {0, 1}]
          

Remove(i, seq) == [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

(***************************************************************************)
(* It's useful to define vars to be the tuple of all variables, for        *)
(* example so we can write [Next]_vars instead of [Next]_<< ...  >>        *)
(***************************************************************************)
vars == << CpuBroker, GpuKernel >>


(***************************************************************************)
(* Initially CpuBroker can equal [value |-> d, bit |-> 1] for any Data     *)
(* value d, and GpuKernel equals CpuBroker.                                *)
(***************************************************************************)
Init == /\ CpuBroker \in [value: Data, bit: {1}] 
        /\ GpuKernel = CpuBroker

(***************************************************************************)
(* When CpuBroker = GpuKernel, the sender can "send" an arbitrary data d   *)
(* item by setting CpuBroker.value to d and complementing CpuBroker.bit.   *)
(* It then waits until the receiver "receives" the message by setting      *)
(* GpuKernel to CpuBroker before it can send its next message.             *)
(* Sending is described by action A and receiving by action B.             *)
(***************************************************************************)
A == /\ CpuBroker = GpuKernel
     /\ \E d \in Data: CpuBroker' = [value |-> d, bit |-> 1 - CpuBroker.bit]
     /\ GpuKernel' = GpuKernel

B == /\ CpuBroker # GpuKernel
     /\ GpuKernel' = CpuBroker
     /\ CpuBroker' = CpuBroker

Next == A \/ B

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* For understanding the spec, it's useful to define formulas that should  *)
(* be invariants and check that they are invariant.  The following         *)
(* invariant Inv asserts that, if CpuBroker and GpuKernel have equal       *)
(* bit fields, then they are equal (which by the invariance of TypeOK      *)
(* implies that they have equal value fields).                             *)
(***************************************************************************)
Inv == (CpuBroker.bit = GpuKernel.bit) => (CpuBroker = GpuKernel)
-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with the addition requirement that it keeps taking     *)
(* steps.                                                                  *)
(***************************************************************************)
FairSpec == Spec /\ WF_vars(Next)
=============================================================================
