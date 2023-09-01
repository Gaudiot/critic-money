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
    CPFS_REGISTERED
PROPERTIES
    ACCOUNT = struct(HOLDER : CPFS, dependents : POW(CPFS), balance : FLOAT)
    CPFS_REGISTERED = {client | client : CPF & (# account . (account : CLIENTS & ( client = account'holder or client : account'dependents)))}
VARIABLES
    CLIENTS
INVARIANT
    CLIENTS: POW(ACCOUNT)
INITIALISATION
    CLIENTS := {}
 
OPERATIONS
    register_new_account(cpf) =
    PRE
        cpf : CPFS &
        cpf :/ CPFS_REGISTERED
    THEN
        CLIENTS := CLIENTS \/ {rec(holder : cpf, dependents : {}, balance : 0)}
    END;
    
    /*
    TODO
    - FAZER O CORPO DA FUNCAO
    */
    register_as_dependent(holder, cpf) =
    PRE
        holder : CPFS_REGISTERED &
        cpf : CPFS &
        cpf :/ CPFS_REGISTERED
    THEN
        CLIENTS := CLIENTS
    END;
    
    /*
    TODO
    - GARANTIR QUE A CONTA TENHA SALDO SUFICIENTE
    - FAZER O CORPO DA FUNCAO
    */
    withdraw(client, amount) = 
    PRE
        client: CPFS_REGISTERED & 
        amount: FLOAT & amount > 0 
    THEN
    
    END;
    
    /*
    TODO
    - FAZER O CORPO DA FUNCAO
    */    
    deposit(client, amount) =
    PRE
        client: CPFS_REGISTERED &
        amount: FLOAT & amount > 0
    THEN
    
    END;
    
    /*
    TODO
    - GARANTIR QUE A CONTA TENHA SALDO SUFICIENTE
    - GARANTIR QUE O SENDER E RECEIVER NÃO SÃO DA MESMA CONTA
    - FAZER O CORPO DA FUNCAO
    */
    transfer(clientSender, clientReceiver, amount) =
    PRE
        clientSender : CPFS_REGISTERED & clientReceiver : CPFS_REGISTERED &
        clientSender /= clientReceiver &
        amount: FLOAT & amount > 0
    THEN
    
    END

END
