MACHINE
    PlaceSector

EXTENDS Objects

VARIABLES
    places, places_sectors
    
INVARIANT
    places <: PLACES &
    places_sectors : places --> SECTORS

INITIALISATION
    places_sectors := {}    ||
    places := {}            

OPERATIONS
    rr <-- create_place(pp, ss)=
    PRE pp : PLACES & ss : SECTORS
        & ss: sectors & pp /: places THEN  
        places := places \/ {pp}                         ||
        places_sectors := places_sectors \/ {pp |-> ss}  ||             
        rr := SalaCadastrada
    END;
   
    ss <-- get_sector(pp)=
    PRE pp: PLACES & pp: places THEN
        ss := places_sectors(pp)
    END
END
