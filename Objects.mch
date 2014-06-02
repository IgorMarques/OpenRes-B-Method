/* Objects
 * Author: 
 * Creation date: 19/05/14
 */
MACHINE
    Objects
    
EXTENDS Sectors

VARIABLES
    objects

INVARIANT
    objects <: OBJECTS
    
INITIALISATION
    objects := {}
    
OPERATIONS
    rr <-- create_object(oo)=
    PRE oo : OBJECTS THEN 
        objects := objects \/ {oo} || 
        rr := ObjetoCadastrado
    END

END
