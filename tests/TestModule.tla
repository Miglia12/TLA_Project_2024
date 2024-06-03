------------------------------ MODULE TestModule ------------------------------
EXTENDS Integers, Sequences

(***************************************************************************)
(* Helper function to find the index of an element in a sequence.          *)
(***************************************************************************)
IndexOf(elem, seq) == 
    CHOOSE i \in 1..Len(seq) : seq[i] = elem

(***************************************************************************)
(* Helper function to remove the first occurrence of an element from a sequence. *)
(***************************************************************************)
RemoveFromSeq(elem, seq) == 
    IF ~ \E i \in 1..Len(seq) : seq[i] = elem THEN seq
    ELSE [i \in 1..(Len(seq) - 1) |-> 
            IF i < IndexOf(elem, seq) THEN seq[i]
            ELSE seq[i + 1]
         ]

(***************************************************************************)
(* Define some test sequences and elements to remove                      *)
(***************************************************************************)
TestSeq1 == <<1, 2, 3>>
TestSeq2 == <<1, 2, 2, 3>>
TestSeq3 == <<1, 3, 2>>

(***************************************************************************)
(* Define expressions to evaluate the RemoveFromSeq function               *)
(***************************************************************************)
TestRemove1 == RemoveFromSeq(2, TestSeq1) \* Expected: <<1, 3>>
TestRemove2 == RemoveFromSeq(2, TestSeq2) \* Expected: <<1, 2, 3>>
TestRemove3 == RemoveFromSeq(2, TestSeq3) \* Expected: <<1, 3>>
TestRemove4 == RemoveFromSeq(4, TestSeq1) \* Expected: <<1, 2, 3>>

=============================================================================
