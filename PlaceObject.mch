MACHINE
    PlaceObject

EXTENDS PlaceSector

VARIABLES
    places_objects, objects_by_place, places_by_object

INVARIANT
    places_objects : places <-> objects &
    objects_by_place <: objects &
    places_by_object <: places
    
INITIALISATION
    places_objects := {}         ||
    objects_by_place := {}       ||
    places_by_object := {}
  
OPERATIONS    
    rr <-- add_obj_to_place(oo, pp)=
    PRE oo : OBJECTS & pp: PLACES 
        & oo: objects & pp: places THEN 
        places_objects := places_objects \/ {pp |-> oo} ||
        rr := Sucesso
    END;
    
    rr <-- initialize_objects_by_place(pp) =
    PRE pp: PLACES THEN 
        objects_by_place := ran({pp} <| places_objects) ||
        rr := Sucesso
    END;
    
    aa, rr <-- next_objects_by_place=
    PRE aa: OBJECTS & objects_by_place /= {} THEN
        ANY xx WHERE xx: objects_by_place THEN
            aa := xx || rr := Sucesso                   ||
            objects_by_place := objects_by_place - {xx}
        END
    END;
    
    rr <-- initialize_places_by_object(oo) =
    PRE oo: OBJECTS THEN 
        places_by_object := dom(places_objects |> {oo}) ||
        rr := Sucesso
    END;
    
    aa, rr <-- next_places_by_object=
    PRE aa: PLACES & places_by_object /= {} THEN
        ANY xx WHERE xx: places_by_object THEN
            aa := xx || rr := Sucesso ||
            places_by_object := places_by_object - {xx}
        END
    END
END
