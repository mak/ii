-module(benchmark).
-export([start/0, loop/3]).

-import(statistics).
-import(ring).

start() ->
    Statistics = statistics:start(),
    Ring = ring:start(self(), Statistics, 5),
    
    receive
        {ring, created, _} ->
            io:format("Ring created\n"),
            {ok, spawn(benchmark, loop, [Statistics, Ring, 1])}
    after
        3000 ->
            io:format("Ring timeout!\n"),
            Ring ! stop,
            Statistics ! stop,
            {error, ring_timeout}
    end.

loop(Statistics, Ring, TokenID) ->
    receive
        {Steps, StopTime} -> 
            Statistics ! {token, start, TokenID, Steps, now()},
            Ring ! {TokenID, Steps, StopTime},
            loop(Statistics, Ring, TokenID + 1);

        stop ->
            Ring ! stop,
            Statistics ! stop
    end.
