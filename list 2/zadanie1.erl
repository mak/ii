-module(zadanie1).
-export([rozklad/1, zaprzyjaznione/1]).


zaprzyjaznione(N) when N > 1->
    [{A, B} || A <- lists:seq(2, N), B <- lists:seq(A, N),
        zaprzyjaznione(A, B)].

zaprzyjaznione(A, B) ->
    S1 = lists:sum(dzielniki(A)),
    S2 = lists:sum(dzielniki(B)),
    (S1 == B) and (S2 == A).


dzielniki(N) when N > 0 -> dzielniki(N, 2, [1]).

dzielniki(N, D, L) when 2 * D > N -> L;
dzielniki(N, D, L) when N rem D == 0 -> 
    dzielniki(N, D + 1, [D|L]);
dzielniki(N, D, L) -> dzielniki(N, D + 1, L).


%%%%%%%%%% ROZKLAD
 
rozklad(N) when is_integer(N) ->
    rozklad(N, 2, []).

rozklad(N, D, L) when D > N -> L;
rozklad(N, D, L) ->
   Pierwsza = pierwsza(D),
   if  
       Pierwsza == true -> 
           Stopien = stopien(N, D),
           if
               Stopien > 0  -> [{D, Stopien} | rozklad(N, D + 1, L)];
               Stopien == 0 -> rozklad(N, D + 1, L)
           end;
       true -> rozklad(N, D + 1, L)
   end.

stopien(0, _) -> 0;
stopien(N, D) -> 
    if 
        (N rem D == 0) -> 1 + stopien(N div D, D);
        true -> 0
    end.

pierwsza(N) when is_integer(N) -> pierwsza(N, 2).

pierwsza(N, D) when (2 * D > N) -> true;
pierwsza(N, D) when (N rem D == 0) -> false;
pierwsza(N, D) -> pierwsza(N, D + 1).

