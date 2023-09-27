/* bank2
 * Author: User
 * Creation date: 25/09/2023
 */
MACHINE
    Bank
    
SETS
    CPFS
CONSTANTS
    ACCOUNT
PROPERTIES
    ACCOUNT = struct(dependents: FIN(CPFS), balance : REAL)
VARIABLES
    CLIENTS    
INVARIANT
    CLIENTS: CPFS +-> ACCOUNT &
    (! cpf . (cpf: dom(CLIENTS) => (CLIENTS(cpf))'balance >= 0.0)) &
    (! cpf . (cpf : dom(CLIENTS) => ( not( # cpf_ . ( cpf_ : dom(CLIENTS) & cpf : (CLIENTS(cpf_))'dependents ) ) ) ) )
    
INITIALISATION
    CLIENTS := {}
    
OPERATIONS
    register_new_account(cpf) =
    PRE
        cpf : CPFS &
        cpf /: dom(CLIENTS) &
        cpf /: union(
            { 
                all_dependents | all_dependents : FIN(CPFS) & ( # cpf_ . (cpf_ : dom(CLIENTS) & (CLIENTS(cpf_))'dependents = all_dependents))
            }
        )
    THEN
        ANY XX WHERE
            XX : FIN(CPFS) &
            XX = {} 
        THEN
            CLIENTS := CLIENTS \/ { cpf |-> rec(dependents: XX, balance: 0.0) }
        END
    END;
    
    register_as_dependent(holder, dependent) =
    PRE
        holder : dom(CLIENTS) &
        dependent : CPFS &
        dependent /: dom(CLIENTS) &
        dependent /: union(
            { 
                all_dependents | all_dependents : FIN(CPFS) & ( # cpf_ . (cpf_ : dom(CLIENTS) & (CLIENTS(cpf_))'dependents = all_dependents))
            }
        )
    THEN
        ANY XX, YY WHERE
            XX : FIN(CPFS) &
            YY : REAL &
            XX = (CLIENTS(holder))'dependents \/ {dependent} &
            YY = (CLIENTS(holder))'balance
        THEN
            CLIENTS := CLIENTS <+ {
                holder |-> rec(
                    dependents: XX,
                    balance: YY
                )
            }
        END
    END;
    
    remove_client(holder) =
    PRE
        holder: dom(CLIENTS)
    THEN
        CLIENTS := {holder} <<| CLIENTS
    END;
    
    remove_dependent(dependent) =
    PRE
        dependent: CPFS &
        dependent: {cpf | cpf : CPFS & (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents))}
    THEN
        ANY holder WHERE
            holder: {hh | hh: dom(CLIENTS) & dependent: (CLIENTS(hh))'dependents}
        THEN
            CLIENTS(holder) := rec(
                dependents: (CLIENTS(holder))'dependents - {dependent},
                balance: (CLIENTS(holder))'balance
            )
        END
    END;
    
    withdraw(client, amount) =
    PRE
        client: CPFS &
        client: {cpf | cpf : CPFS & (cpf: dom(CLIENTS) or (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents)))} &
        amount: REAL & amount > 0.0 &
        (# holder . (holder: dom(CLIENTS) & (client = holder or client: (CLIENTS(holder))'dependents) & (CLIENTS(holder))'balance >= amount))
    THEN
        ANY holder, XX, YY WHERE
            holder: {cpf | cpf: dom(CLIENTS) & (client = cpf or client: (CLIENTS(cpf))'dependents)} &
            XX : FIN(CPFS) &
            XX = (CLIENTS(holder))'dependents &
            YY : REAL &
            YY = (CLIENTS(holder))'balance - amount
        THEN   
            CLIENTS := CLIENTS <+ 
                {
                    holder |-> rec(
                        dependents: XX,
                        balance: YY
                    )
                }
        END         
    END;
    
    deposit(client, amount) =
    PRE
        client: CPFS &
        client: {cpf | cpf : CPFS & (cpf: dom(CLIENTS) or (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents)))} &
        amount: REAL & amount > 0.0
    THEN
        ANY holder, XX, YY WHERE
            holder: {cpf | cpf: dom(CLIENTS) & (client = cpf or client: (CLIENTS(cpf))'dependents)} &
            XX : FIN(CPFS) &
            XX = (CLIENTS(holder))'dependents &
            YY : REAL &
            YY = (CLIENTS(holder))'balance + amount
        THEN   
            CLIENTS := CLIENTS <+ 
                {
                    holder |-> rec(
                        dependents: XX,
                        balance: YY
                    )
                }
        END  
    END;
    
    transfer(clientSender, clientReceiver, amount) =
    PRE
        clientSender: CPFS & clientReceiver: CPFS &
        clientSender /= clientReceiver &
        card({holder | holder: dom(CLIENTS) & ((clientSender = holder or clientReceiver = holder) or (clientSender: (CLIENTS(holder))'dependents or clientSender: (CLIENTS(holder))'dependents))}) = 2 &
        amount: REAL & amount > 0.0 &
        (# holder . (holder: dom(CLIENTS) & (clientSender = holder or clientSender: (CLIENTS(holder))'dependents) & (CLIENTS(holder))'balance >= amount))
    THEN
        ANY holderSender, holderReceiver, XX, YY WHERE
            holderSender: {holder | holder: dom(CLIENTS) & (clientSender = holder or clientSender: (CLIENTS(holder))'dependents)} &
            holderReceiver: {holder | holder: dom(CLIENTS) & (clientReceiver = holder or clientReceiver: (CLIENTS(holder))'dependents)} &
            holderSender /= holderReceiver &
            XX : ACCOUNT &
            YY : ACCOUNT &
            XX = rec( dependents: (CLIENTS(holderSender))'dependents, balance: (CLIENTS(holderSender))'balance - amount ) &
            YY = rec( dependents: (CLIENTS(holderReceiver))'dependents, balance: (CLIENTS(holderReceiver))'balance + amount )
        THEN   
            CLIENTS := CLIENTS <+ 
                {
                    holderSender |-> XX,
                    holderReceiver |-> YY
                }
        END
    END;
    
    cc <-- check_balance(client) =
    PRE
        client: CPFS & 
        client: {cpf | cpf : CPFS & (cpf: dom(CLIENTS) or (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents)))}
    THEN
        ANY holder WHERE
            holder: {hh | hh: dom(CLIENTS) & (client = hh or client: (CLIENTS(hh))'dependents)}
        THEN
            cc := (CLIENTS(holder))'balance
        END
    END
END
