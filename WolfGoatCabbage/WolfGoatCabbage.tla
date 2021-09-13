-------------------------- MODULE WolfGoatCabbage --------------------------
(* 
Once upon a time a farmer went to a market and purchased a wolf, a goat, and a cabbage. 
On his way home, the farmer came to the bank of a river and rented a boat. But crossing the 
river by boat, the farmer could carry only himself and a single one of his purchases: the wolf, 
the goat, or the cabbage.

If left unattended together, the wolf would eat the goat, or the goat would eat the cabbage.

The farmer's challenge was to carry himself and his purchases to the far bank of the river, 
leaving each purchase intact. How did he do it?
*)
EXTENDS Sequences

(*
  leftB - river bank where farmer came,
  rightB - far river bank,
  boatPos - boat position
*)
VARIABLES leftB, rightB, boatPos
vars == << leftB, rightB, boatPos >>

TypeOK == 
    /\ boatPos \in {"l","r"}
    /\ \A x \in leftB: x \in {"w","g","c"}
    /\ \A x \in rightB: x \in {"w","g","c"}
            
Init == 
    /\ leftB = {"w","g","c"}
    /\ rightB = {}
    /\ boatPos = "l"

CanCross(place) == 
    /\ ~({"w","g"} \subseteq place) 
    /\ ~({"g","c"} \subseteq place)

GotoRight == 
    /\ boatPos = "l"
    /\ CanCross(leftB)
    /\ boatPos' = "r"
    /\ UNCHANGED <<leftB, rightB>>

GotoLeft ==  
    /\ boatPos = "r"
    /\ CanCross(rightB)
    /\ boatPos' = "l"
    /\ UNCHANGED <<leftB, rightB>>

Move(x, from, to) == 
    /\ from' = from \ {x}
    /\ to' = to \union {x}
                         
MovetoRight(x) == 
    /\ boatPos = "l"
    /\ CanCross(leftB \ {x}) 
    /\ boatPos' = "r" 
    /\ Move(x, leftB, rightB)
                
MovetoLeft(x)  == 
    /\ boatPos = "r"
    /\ CanCross(rightB \ {x}) 
    /\ boatPos' = "l"
    /\ Move(x, rightB, leftB)
                
Next == 
    \/ \E x \in leftB: MovetoRight(x)
    \/ GotoRight
    \/ \E x \in rightB: MovetoLeft(x)
    \/ GotoLeft

Spec == Init /\ [][Next]_<<vars>>

THEOREM Spec => TypeOK
=============================================================================
\* Modification History
\* Last modified Fri Sep 10 15:23:16 MSK 2021 by s.elin
\* Created Sun Sep 05 09:59:38 MSK 2021 by s.elin
