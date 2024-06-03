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
(* Helper function to check if an element is not in a sequence.            *)
(***************************************************************************)
NotInSeq(elem, seq) == \A i \in 1..Len(seq) : elem # seq[i]

(***************************************************************************)
(* Test Sequences                                                          *)
(***************************************************************************)
TestSeq1 == <<1, 2, 3>>
TestSeq2 == <<1, 2, 2, 3>>
TestSeq3 == <<1, 3, 2>>
TestSeq4 == <<>>

(***************************************************************************)
(* Tests for IndexOf function                                              *)
(***************************************************************************)
TestIndexOf1 == IndexOf(3, TestSeq1) \* Expected: 3
TestIndexOf2 == IndexOf(2, TestSeq2) \* Expected: 2
TestIndexOf3 == IndexOf(1, TestSeq3) \* Expected: 1
TestIndexOf4 == IF \E i \in 1..Len(TestSeq4) : TestSeq4[i] = 1 THEN IndexOf(1, TestSeq4) ELSE "Not Found" \* Expected: "Not Found"
TestIndexOf5 == IF \E i \in 1..Len(TestSeq1) : TestSeq1[i] = 4 THEN IndexOf(4, TestSeq1) ELSE "Not Found" \* Expected: "Not Found"

(***************************************************************************)
(* Tests for RemoveFromSeq function                                        *)
(***************************************************************************)
TestRemove1 == RemoveFromSeq(2, TestSeq1) \* Expected: <<1, 3>>
TestRemove2 == RemoveFromSeq(2, TestSeq2) \* Expected: <<1, 2, 3>>
TestRemove3 == RemoveFromSeq(2, TestSeq3) \* Expected: <<1, 3>>
TestRemove4 == RemoveFromSeq(4, TestSeq1) \* Expected: <<1, 2, 3>>
TestRemove5 == RemoveFromSeq(1, TestSeq4) \* Expected: <<>>

(***************************************************************************)
(* Tests for NotInSeq function                                             *)
(***************************************************************************)
TestNotInSeq1 == NotInSeq(2, TestSeq1) \* Expected: FALSE
TestNotInSeq2 == NotInSeq(4, TestSeq1) \* Expected: TRUE
TestNotInSeq3 == NotInSeq(1, TestSeq4) \* Expected: TRUE
TestNotInSeq4 == NotInSeq(2, TestSeq4) \* Expected: TRUE

=============================================================================
