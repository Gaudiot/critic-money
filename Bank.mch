/* Bank
 * Author: Victor Gaudiot & Matheus Isidoro
 * Creation date: 05/09/23
 */
MACHINE
    Bank
SETS
    CPFS
CONSTANTS
    ACCOUNT
PROPERTIES
    ACCOUNT = struct(dependents: POW(CPFS), balance : REAL)
VARIABLES
    CLIENTS    
INVARIANT
    CLIENTS: CPFS +-> ACCOUNT &
    (! cpf . (cpf: dom(CLIENTS) => (CLIENTS(cpf))'balance >= 0.0)) &
    (! cpf . (cpf : dom(CLIENTS) => ( not( # cpf_ . ( cpf_ : dom(CLIENTS) & cpf /= cpf_ & cpf : (CLIENTS(cpf_))'dependents ) ) ) ) )
    
INITIALISATION
    CLIENTS := {}
    
OPERATIONS    
    register_new_account(cpf) =
    PRE
        cpf : CPFS &
        cpf /: dom(CLIENTS) &
        cpf /: union(
            { 
                all_dependents | all_dependents : POW(CPFS) & ( # cpf_ . (cpf_ : dom(CLIENTS) & (CLIENTS(cpf_))'dependents = all_dependents))
            }
        )
    THEN
        ANY XX WHERE
            XX : POW(CPFS) &
            XX = {} 
        THEN
            CLIENTS := CLIENTS <+
                {
                    cpf |-> rec(dependents: XX, balance: 0.0)
                }
        END
    END;
    
    register_as_dependent(holder, dependent) =
    PRE
        holder : dom(CLIENTS) &
        dependent : CPFS &
        dependent /: dom(CLIENTS) &
        dependent /: union(
            { 
                all_dependents | all_dependents : POW(CPFS) & ( # cpf_ . (cpf_ : dom(CLIENTS) & (CLIENTS(cpf_))'dependents = all_dependents))
            }
        )
    THEN
        CLIENTS := CLIENTS <+
            {
                holder |-> rec(
                    dependents: (CLIENTS(holder))'dependents \/ {dependent},
                    balance: (CLIENTS(holder))'balance
                )
            }
    END; 
    
    withdraw(client, amount) =
    PRE
        client: CPFS &
        client: {cpf | cpf : CPFS & (cpf: dom(CLIENTS) or (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents)))} &
        amount: REAL & amount > 0.0
    THEN
        ANY holder WHERE
            holder: {cpf | cpf: dom(CLIENTS) & (client = cpf or client: (CLIENTS(cpf))'dependents)}
            
        THEN   
            CLIENTS := CLIENTS <+ 
                {
                    holder |-> rec(
                        dependents: (CLIENTS(holder))'dependents,
                        balance: (CLIENTS(holder))'balance - amount
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
        ANY holder WHERE
            holder: {cpf | cpf: dom(CLIENTS) & (client = cpf or client: (CLIENTS(cpf))'dependents)}
            
        THEN   
            CLIENTS := CLIENTS <+ 
                {
                    holder |-> rec(
                        dependents: (CLIENTS(holder))'dependents,
                        balance: (CLIENTS(holder))'balance + amount
                    )
                }
        END  
    END;
    
    transfer(clientSender, clientReceiver, amount) =
    PRE
        clientSender: CPFS & clientReceiver: CPFS &
        card({holder | holder: dom(CLIENTS) & ((clientSender = holder or clientReceiver = holder) or (clientSender: (CLIENTS(holder))'dependents or clientSender: (CLIENTS(holder))'dependents))}) = 2 &
        clientSender /= clientReceiver &
        amount: REAL & amount > 0.0 &
        (# holder . (holder: dom(CLIENTS) & (clientSender = holder or clientSender: (CLIENTS(holder))'dependents) & (CLIENTS(holder))'balance >= amount))
    THEN
        ANY holderSender, holderReceiver WHERE
            holderSender: {holder | holder: dom(CLIENTS) & (clientSender = holder or clientSender: (CLIENTS(holder))'dependents)} &
            holderReceiver: {holder | holder: dom(CLIENTS) & (clientReceiver = holder or clientReceiver: (CLIENTS(holder))'dependents)}
        THEN   
            CLIENTS := CLIENTS <+ 
                {
                    holderSender |-> rec(
                        dependents: (CLIENTS(holderSender))'dependents,
                        balance: (CLIENTS(holderSender))'balance - amount
                    ),
                    holderReceiver |-> rec(
                        dependents: (CLIENTS(holderReceiver))'dependents,
                        balance: (CLIENTS(holderReceiver))'balance + amount
                    )
                }
        END
    END
END
