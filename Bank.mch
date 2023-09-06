/* BankR
 * Author: 
 * Creation date: 05/09/23
 */
MACHINE
    BankR
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
            CLIENTS := CLIENTS \/
                {
                    cpf |-> rec(dependents: XX, balance: 0.0)
                }
        END
    END;
    
    register_as_dependent(holder, dependent) =
    PRE
        holder : CPFS &
        holder : dom(CLIENTS) &
        dependent : CPFS &
        dependent /: dom(CLIENTS) &
        dependent /: union({all_dependents | all_dependents : POW(CPFS) & (# cpf_ . (cpf_ : dom(CLIENTS) & (CLIENTS(cpf_))'dependents = all_dependents))})
    THEN
        ANY XX WHERE
            XX : ACCOUNT &
            XX = rec( dependents: ((CLIENTS(holder))'dependents \/ {dependent}), balance: (CLIENTS(holder))'balance )
        THEN
        CLIENTS := CLIENTS <+
            {
                holder |-> XX
            }
        END
    END; 
    
    withdraw(client, amount) =
    PRE
        client: CPFS &
        client: {cpf | cpf : CPFS & (cpf: dom(CLIENTS) or (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents)))} &
        amount: REAL & amount > 0.0
    THEN
        ANY holder, XX WHERE
            holder: CPFS & holder: dom(CLIENTS) &
            (
                (client = holder or
                client: (CLIENTS(holder))'dependents) &
                (CLIENTS(holder))'balance > amount
            ) &
            XX : ACCOUNT &
            XX = rec( dependents: (CLIENTS(holder))'dependents, balance: (CLIENTS(holder))'balance - amount )
        THEN 
            CLIENTS := CLIENTS <+ 
                {
                    holder |-> XX
                }
        END        
    END;
    
    deposit(client, amount) =
    PRE
        client: {cpf | cpf : CPFS & (cpf: dom(CLIENTS) or (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents)))} &
        amount: REAL & amount > 0.0
    THEN
        ANY holder, XX WHERE
            holder: CPFS & holder: dom(CLIENTS) &
            (
                client = holder or
                client: (CLIENTS(holder))'dependents
            ) &
            XX : ACCOUNT &
            XX = rec( dependents: (CLIENTS(holder))'dependents, balance: (CLIENTS(holder))'balance + amount )
            
        THEN   
            CLIENTS := CLIENTS <+ 
                {
                    holder |-> XX
                }
        END  
    END;
    
    transfer(clientSender, clientReceiver, amount) =
    PRE
        clientSender: CPFS &
        clientReceiver: CPFS &
        clientSender : {cpf | cpf : CPFS & ((cpf: dom(CLIENTS) & clientReceiver /: (CLIENTS(cpf))'dependents) or (# cpf_ . (cpf_ : dom(CLIENTS) & cpf : (CLIENTS(cpf_))'dependents & clientReceiver /: (CLIENTS(cpf_))'dependents)))} &
        clientReceiver : {cpf | cpf : CPFS & ((cpf: dom(CLIENTS) & clientSender /: (CLIENTS(cpf))'dependents) or (# cpf_ . (cpf_ : dom(CLIENTS) & cpf : (CLIENTS(cpf_))'dependents & clientSender /: (CLIENTS(cpf_))'dependents)))} &
        clientSender /= clientReceiver &
        amount: REAL & amount > 0.0
    THEN
        ANY holderSender, holderReceiver, XX, YY WHERE
            holderSender : CPFS &
            holderReceiver : CPFS &
            holderSender : dom(CLIENTS) &
            holderReceiver : dom(CLIENTS) &
            holderSender /= holderReceiver &
            (
                ( clientSender = holderSender or
                clientSender : (CLIENTS(holderSender))'dependents ) &
                (CLIENTS(holderSender))'balance >= amount
            ) &
            (
                clientReceiver = holderReceiver or
                clientReceiver : (CLIENTS(holderReceiver))'dependents
            ) &
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

