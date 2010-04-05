-module(benchmark).
-export([start/0, loop/4]).

-import(statistics).
-import(ring).

start() ->
    Statistics = statistics:start(),
    {ok, spawn(benchmark, loop, [Statistics, self(), 1, 1])}.

loop(Statistics, Ring, TokenID, RingID) ->
    receive
        {token, Steps, undefined} ->
            Ring ! {TokenID, Steps, undefined},
            loop(Statistics, Ring, TokenID + 1, RingID);

        {token, Steps, Seconds} -> 
            {MegaSec, Sec, Milisec} = now(),
            StopTime = {MegaSec + ((Sec + Seconds) div 1000000),
               (Sec + Seconds) rem 1000000, Milisec},
            Ring ! {TokenID, Steps, StopTime},
            loop(Statistics, Ring, TokenID + 1, RingID);

        {start, Size} ->
            NewRing = ring:start(RingID, self(), Statistics, Size),
            receive 
                {ring, created, RingID} ->
                    io:format("Ring ~w created with size: ~w\n", [RingID, Size]),
                    Ring ! stop,
                    loop(Statistics, NewRing, TokenID, RingID + 1)
            after
                3000 -> 
                    io:format("Ring ~w timeout!\n", [RingID]),
                    NewRing ! stop,
                    loop(Statistics, Ring, TokenID, RingID)
            end;
            
        stop ->
            Statistics ! stop,
            Ring ! stop,
            receive
                {ring, destroyed, DestroyedRingID} ->
                    io:format("Ring ~w destroyed\n", [DestroyedRingID])
            end
    end.
