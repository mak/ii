-module(zadanie2).
-export([isum/1, imax/1]).

isum(L) when is_list(L) -> isum(L, 0).

isum([], N) -> N;
isum([H|T], N) when is_integer(H) -> isum(T, N+H).

imax([H]) when is_integer(H) -> H;
imax([H|T]) -> imax(T, H).

imax([], M) -> M;
imax([H|T], M) when is_integer(H) -> 
    if
        H > M -> imax(T, H);
        true  -> imax(T, M)
    end. 
