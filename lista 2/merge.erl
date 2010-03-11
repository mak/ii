#!/usr/bin/env escript


-import(lists).

main(Args) -> 
    L = lists:map(fun(X) -> list_to_integer(X) end, Args),
    io:format("~w\n", [mergesort(L)]).

mergesort([]) -> [];
mergesort([X]) -> [X];
mergesort(L) when is_list(L) ->
    {A, B} = split(L),
    merge(mergesort(A), mergesort(B)).

split(L) when is_list(L) -> split(L, [], []).

split([], A, B) -> {A, B};
split([X], A, B) -> {[X|A], B};
split([X,Y|T], A, B) -> split(T, [X|A], [Y|B]).

merge([], X) -> X;
merge(X, []) -> X;
merge([X1|T1], [X2|T2]) ->
    if
        X1 < X2 -> [X1 | merge(T1, [X2|T2])];
        true    -> [X2 | merge([X1|T1], T2)]
    end.
