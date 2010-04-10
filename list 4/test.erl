-module(test).
-compile(export_all).

-import(statistics).
-import(benchmark).

test() ->
    S = statistics:start(),
    B = benchmark:start(S),
    B ! {start, 5},
    B ! list_ring,
    B ! {start, 15},
    B ! {token, 1, 10, undefined},
    B ! {token, 2, 10, undefined},
    B ! list_ring,
    {S, B}.
