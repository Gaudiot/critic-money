MACHINE phonebook2

VARIABLES db, active, lock

INVARIANT
	lock : BOOL &
	db : STRING +-> NATURAL &
	active : POW(STRING)

INITIALISATION
	db := {} || active := {} ||
	lock := FALSE

OPERATIONS

add(name, nr) =
	PRE
		name : STRING & nr : NATURAL &
		name /: dom(db)  & lock = FALSE
	THEN
		db := db \/ { name |-> nr }
	END;

remove(name, nr) =
	PRE
	  	name : STRING & nr : NATURAL &
		name |-> nr : db & lock = FALSE
	THEN
		db := db \  { name |-> nr }
	END;

nr <-- lookup(name) =
	PRE
		name : STRING
	THEN
		nr := db(name)
	END;

update(name, nr) =
	PRE
		name : STRING & nr : NATURAL &
		name : dom(db) & lock = FALSE
	THEN
		db(name) := nr
	END;

toggle(name) =
        SELECT
                name : dom(db)
        THEN
                IF name : active THEN
                   active := active \ {name}
                ELSE
                   active := active \/ {name}
                END
        END;

deactivate(name) =
	PRE
		name : active & lock = FALSE
	THEN
		active := active \ {name}
	END;

activate(name) =
	PRE
		name : dom(db) & lock = FALSE
	THEN
		active := active \/ {name}
	END;

lock =
	PRE
		lock = FALSE
	THEN
		lock := TRUE
	END;

unlock =
	PRE
		lock = TRUE
	THEN
		lock := FALSE
	END

END
