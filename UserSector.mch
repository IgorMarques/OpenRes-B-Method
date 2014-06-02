MACHINE
    UserSector

EXTENDS PlaceObject

VARIABLES
    approvers, users_sectors, reservers
    
INVARIANT
    reservers <: RESERVERS &
    users_sectors  : reservers --> SECTORS & 
    approvers     <: reservers
    
INITIALISATION
    users_sectors := {}          ||
    approvers := {}              ||
    reservers := {}
    
OPERATIONS
    rr <-- create_reserver(rs, ss)=
    PRE rs : RESERVERS & ss : SECTORS & ss: sectors & rs /: reservers THEN
        reservers := reservers \/ {rs}                || 
        users_sectors := users_sectors \/ {rs |-> ss} ||
        rr := ReservanteCadastrado
    END;
    
    rr <-- promote_user(rs) =
    PRE rs: RESERVERS & rs: reservers THEN
        approvers := approvers \/ {rs} ||
        rr := PromovidoComSucesso
    END
    
END
