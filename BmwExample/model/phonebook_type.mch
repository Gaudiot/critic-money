MACHINE phonebook2

SETS TYPE = {work, home}

VARIABLES db, active, lock

INVARIANT
	lock : BOOL &
	db : STRING +-> (TYPE +-> NATURAL) &
	active : POW(STRING)

INITIALISATION
	db := {} || active := {} || lock := FALSE

OPERATIONS

add(name, nr, type) =
	PRE
		name : STRING & nr : NATURAL & type: TYPE &
		name /: dom(db)  & lock = FALSE
	THEN
		db := db \/ { name |-> { type |-> nr } }
	END;

remove(name, nr, type) =
	PRE
	  	name : STRING & nr : NATURAL & type : TYPE &
		name |-> { type |-> nr } : db & lock = FALSE
	THEN
		db := db \  { name |-> { type |-> nr } }
	END;

nr <-- lookup(name, type) =
	PRE
		name : STRING & type : TYPE
	THEN
		nr := db(name)(type)
	END;

update(name, nr, type) =
	PRE
		name : STRING & nr : NATURAL  & type : TYPE &
		name : dom(db) & lock = FALSE
	THEN
		db(name)(type) := nr
	END;

set_inactive(name) =
	PRE
		name : active & lock = FALSE
	THEN
		active := active \ {name}
	END;

set_active(name) =
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
