/* Bank
 * Author: Gaudiot, Matheus Isidoro
 * Creation date: 17/08/2023
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
    CLIENTS: CPFS +-> ACCOUNT
//    GARANTIR QUE  UM CPF SÓ POSSA ESTAR ASSOCIADO A UMA ÚNICA CONTA
//    GARANTIR QUE O SALDO NUNCA POSSA FICAR NEGATIVO
INITIALISATION
    CLIENTS := {}
 
OPERATIONS    
    register_new_account(cpf) =
    PRE
        cpf : CPFS &
        cpf /: dom(CLIENTS) & cpf /: union({all_dependents | all_dependents : POW(CPFS) & (# cpf_ . (cpf_ : dom(CLIENTS) & (CLIENTS(cpf_))'dependents = all_dependents))})
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
    
    /*
    TODO
    - FAZER O CORPO DA FUNCAO
    */
    register_as_dependent(holder, dependent) =
    PRE
        holder : CPFS & holder : dom(CLIENTS) &
        dependent : CPFS & holder /= dependent &
        dependent /: dom(CLIENTS) & dependent /: union({all_dependents | all_dependents : POW(CPFS) & (# cpf_ . (cpf_ : dom(CLIENTS) & (CLIENTS(cpf_))'dependents = all_dependents))})
    THEN
        CLIENTS := CLIENTS <+
            {
                holder |-> rec(
                    dependents:((CLIENTS(holder))'dependents \/ {dependent}),
                    balance: (CLIENTS(holder))'balance)
            }
    END ; 
    
    /*
    TODO
    - GARANTIR QUE A CONTA TENHA SALDO SUFICIENTE
    - FAZER O CORPO DA FUNCAO
    */
    withdraw(client, amount) =
    PRE
        client: CPFS &
        client: {cpf | cpf : CPFS & (cpf: dom(CLIENTS) or (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents)))} &
        amount: REAL & amount > 0.0
    THEN
        ANY holder WHERE
            holder: CPFS & holder: dom(CLIENTS) &
            (
                client = holder or
                client: (CLIENTS(holder))'dependents
            )
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
    
    /*
    TODO
    - FAZER O CORPO DA FUNCAO
    */
    deposit(client, amount) =
    PRE
        client: CPFS &
        client: {cpf | cpf : CPFS & (cpf: dom(CLIENTS) or (#cpf_ . (cpf_ : dom(CLIENTS) & cpf: (CLIENTS(cpf_))'dependents)))} &
        amount: REAL & amount > 0.0
    THEN
        ANY holder WHERE
            holder: CPFS & holder: dom(CLIENTS) &
            (
                client = holder or
                client: (CLIENTS(holder))'dependents
            )
        THEN  
            ANY holder WHERE
                holder: CPFS & holder: dom(CLIENTS) &
                (
                    client = holder or
                    client: (CLIENTS(holder))'dependents
                )
            THEN        
            CLIENTS := CLIENTS <+ 
                {
                    holder |-> rec(
                        dependents: (CLIENTS(holder))'dependents,
                        balance: (CLIENTS(holder))'balance + amount
                    )
                }
            END 
        END  
    END
//    
//    /*
//    TODO
//    - GARANTIR QUE A CONTA TENHA SALDO SUFICIENTE
//    - GARANTIR QUE O SENDER E RECEIVER NÃO SÃO DA MESMA CONTA
//    - FAZER O CORPO DA FUNCAO
//    */
//    transfer(clientSender, clientReceiver, amount) =
//    PRE
//        clientSender : CPFS_REGISTERED & clientReceiver : CPFS_REGISTERED &
//        clientSender /= clientReceiver &
//        amount: REAL & amount > 0
//    THEN
//        CLIENTS := CLIENTS
//    END
END
