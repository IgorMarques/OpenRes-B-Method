MACHINE
    Sectors

EXTENDS Definitions

VARIABLES
    sectors
    
INVARIANT
    sectors <: SECTORS
    
INITIALISATION
    sectors := {}
    
OPERATIONS
    rr <-- create_sector(ss)=
    PRE ss : SECTORS THEN
        sectors := sectors \/ {ss} || 
        rr := SetorCadastrado
    END
    
END
