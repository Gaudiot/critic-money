/* Bank
 * Author: Gaudiot, Matheus Isidoro
 * Creation date: 17/08/2023
 */
MACHINE
    Bank
    
SETS
    CLIENTS
VARIABLES
    ACCOUNTS
INVARIANT
    ACCOUNTS : CLIENTS +-> INTEGER
INITIALISATION
    ACCOUNTS := {}
 
OPERATIONS
    registration(client, amount) =
    PRE
        client : CLIENTS &
        amount: INTEGER &
        client /: dom(ACCOUNTS) &
        amount > 0
    THEN
        ACCOUNTS := ACCOUNTS \/ {client |-> amount}
    END;
    
    withdraw(client, amount) = 
    PRE
        client: CLIENTS & 
        amount: INTEGER &
        amount > 0 &
        client : dom(ACCOUNTS) &
        ACCOUNTS(client) >= amount
    THEN
        ACCOUNTS := ACCOUNTS <+
            {
                client |-> ACCOUNTS(client) - amount
            }
    END;
    
    deposit(client, amount) =
    PRE
        client: CLIENTS &
        client : dom(ACCOUNTS) &
        amount: INTEGER &
        amount > 0
    THEN
        ACCOUNTS := ACCOUNTS <+
            {
                client |-> ACCOUNTS(client) + amount
            }
    END;
    
    transfer(clientSender, clientReceiver, amount) =
    PRE
        clientSender : CLIENTS &
        clientReceiver : CLIENTS &
        clientSender : dom(ACCOUNTS) &
        clientReceiver : dom(ACCOUNTS) &
        clientSender /= clientReceiver &
        amount: INTEGER &
        amount > 0 &
        ACCOUNTS(clientSender) >= amount
    THEN
        ACCOUNTS := ACCOUNTS <+
            {
                clientSender |-> ACCOUNTS(clientSender) - amount,
                clientReceiver |-> ACCOUNTS(clientReceiver) + amount
            }
    END

END

