/* Bank
 * Author: Victor Gaudiot & Matheus Isidoro
 * Creation date: 05/09/23
 */
MACHINE
    Bank
	
CONSTANTS
    ACCOUNT
PROPERTIES
    ACCOUNT = struct(dependents: FIN(STRING), balance : INTEGER)
VARIABLES
    CLIENTS    
INVARIANT
    CLIENTS: STRING +-> ACCOUNT &
    (! cpf . (cpf: dom(CLIENTS) => (CLIENTS(cpf))'balance >= 0)) &
    (! cpf . (cpf : dom(CLIENTS) => ( not( # cpf_ . ( cpf_ : dom(CLIENTS) & cpf : (CLIENTS(cpf_))'dependents ) ) ) ) )
    
INITIALISATION
    CLIENTS := {}
    
OPERATIONS    
    register_new_account(cpf) =
    PRE
        cpf : STRING &
        cpf /: dom(CLIENTS) &
        cpf /: union(
            { 
                all_dependents | all_dependents : FIN(STRING) & ( # cpf_ . (cpf_ : dom(CLIENTS) & (CLIENTS(cpf_))'dependents = all_dependents))
            }
        )
    THEN
        ANY XX WHERE
            XX : FIN(STRING) &
            XX = {} 
        THEN
            CLIENTS := CLIENTS <+
                {
                    cpf |-> rec(dependents: XX, balance: 0)
                }
        END
    END;
    
    register_as_dependent(holder, dependent) =
    PRE
        holder : dom(CLIENTS) &
        dependent : STRING &
        dependent /: dom(CLIENTS) &
        dependent /: union(
            { 
                all_dependents | all_dependents : FIN(STRING) & ( # cpf_ . (cpf_ : dom(CLIENTS) & (CLIENTS(cpf_))'dependents = all_dependents))
            }
        )
    THEN
        ANY XX, YY WHERE
            XX : FIN(STRING) &
            YY : INTEGER &
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
    
    withdraw(client, amount) =
    PRE
        client: STRING &
        client: {cpf | cpf : STRING & (cpf: dom(CLIENTS) or (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents)))} &
        amount: INTEGER & amount > 0 &
        (# holder . (holder: dom(CLIENTS) & (client = holder or client: (CLIENTS(holder))'dependents) & (CLIENTS(holder))'balance >= amount))
    THEN
        ANY holder, XX, YY WHERE
            holder: {cpf | cpf: dom(CLIENTS) & (client = cpf or client: (CLIENTS(cpf))'dependents)} &
            XX : FIN(STRING) &
            XX = (CLIENTS(holder))'dependents &
            YY : INTEGER &
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
        client: STRING &
        client: {cpf | cpf : STRING & (cpf: dom(CLIENTS) or (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents)))} &
        amount: INTEGER & amount > 0
    THEN
        ANY holder, XX, YY WHERE
            holder: {cpf | cpf: dom(CLIENTS) & (client = cpf or client: (CLIENTS(cpf))'dependents)} &
            XX : FIN(STRING) &
            XX = (CLIENTS(holder))'dependents &
            YY : INTEGER &
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
        clientSender: STRING & clientReceiver: STRING &
        clientSender /= clientReceiver &
        card({holder | holder: dom(CLIENTS) & ((clientSender = holder or clientReceiver = holder) or (clientSender: (CLIENTS(holder))'dependents or clientSender: (CLIENTS(holder))'dependents))}) = 2 &
        amount: INTEGER & amount > 0 &
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
    END
END
