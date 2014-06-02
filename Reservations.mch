MACHINE
    Reservations

EXTENDS UserSector

VARIABLES
    reservations,
    approved_reservations,

    reservations_list

INVARIANT
    reservations   : RESERVERS <-> (PLACES * SLOTS) &                                            

    approved_reservations : (places * SLOTS)  +-> reservers &    
    reservations_list <: reservations
    
INITIALISATION

    reservations := {}           ||
    approved_reservations := {}  ||
    
    reservations_list := {}
    
OPERATIONS
      
    rr <-- create_reservation(rs, pp, sl) =
    PRE rs : RESERVERS & pp: PLACES & sl : SLOTS
        & rs : reservers & pp: places THEN
        reservations := reservations \/ { rs |-> (pp, sl) } ||
        rr := ReservaCadastrada
    END;
    
    rr <-- initialize_reservations_by_user(uu)=
    PRE uu: RESERVERS & uu: dom(reservations) THEN
        reservations_list := {uu} <| reservations ||
        rr := Sucesso
    END;
    
    rr <-- initialize_reservations_by_place(pp) =
    PRE pp: PLACES & pp: places THEN 
        reservations_list := reservations |> ({pp} * SLOTS) ||         
        rr := Sucesso
    END;
    
    ur, pp, ss, rr <-- next_reservation(uu) =
    PRE uu: RESERVERS & uu: reservers & reservations_list /= {} THEN
        ANY xx, yy WHERE xx: dom(ran({uu} <| reservations)) 
            & yy: ran(ran({uu} <| reservations)) THEN
            ur := uu || pp := xx || ss := yy ||
            rr := Sucesso || 
            reservations_list := reservations_list - {uu |-> (xx, yy)}            
        END
    END;
    
    rr <-- approve_reservation(ur, pp, ss, uu)=
    PRE ur: RESERVERS & pp: PLACES & ss: SLOTS 
        & (ur |-> (pp, ss)): reservations &
        (pp, ss) /: dom(approved_reservations)
        & uu: RESERVERS & uu: approvers THEN
        approved_reservations := approved_reservations \/ {(pp, ss) |-> ur} ||
        rr := ReservaAprovada
    END;

    rr <-- reject_reservation(ur, pp, ss, uu)=
    PRE ur: RESERVERS & pp: PLACES & ss: SLOTS 
        & (ur |-> (pp, ss)): reservations & uu: RESERVERS 
        & uu: approvers THEN
        reservations_list := {}                                            ||
        reservations := reservations - {ur |-> (pp, ss)}                   ||
        approved_reservations := approved_reservations - {(pp, ss) |-> ur} ||
        rr := ReservaRejeitada
    END
END
