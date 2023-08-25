/* Bank
 * Author: Gaudiot, Matheus Isidoro
 * Creation date: 17/08/2023
 */
MACHINE
    Bank
    
SETS
    CPFS
VARIABLES
    CLIENTS
    BALANCE
INVARIANT
    CLIENTS: POW(CPFS)
    BALANCE : CLIENTS --> FLOAT
INITIALISATION
    CLIENTS := {}
    BALANCE := {}
 
OPERATIONS
    registration(cpf, amount) =
    PRE
        cpf : CPFS & cpf /: CLIENTS &
        amount: FLOAT & amount >= 0.0
    THEN
        BALANCE := BALANCE \/ {cpf |-> amount}
    END;
    
    withdraw(client, amount) = 
    PRE
        client: CLIENTS & 
        amount: FLOAT & amount > 0 &
        BALANCE(client) >= amount
    THEN
        BALANCE := BALANCE <+
            {
                client |-> BALANCE(client) - amount
            }
    END;
    
    deposit(client, amount) =
    PRE
        client: CLIENTS &
        client : dom(BALANCE) &
        amount: INTEGER &
        amount > 0
    THEN
        BALANCE := BALANCE <+
            {
                client |-> BALANCE(client) + amount
            }
    END;
    
    transfer(clientSender, clientReceiver, amount) =
    PRE
        clientSender : CLIENTS & clientReceiver : CLIENTS &
        clientSender /= clientReceiver &
        amount: INTEGER & amount > 0 &
        BALANCE(clientSender) >= amount
    THEN
        BALANCE := BALANCE <+
            {
                clientSender |-> BALANCE(clientSender) - amount,
                clientReceiver |-> BALANCE(clientReceiver) + amount
            }
    END

END
