-module(benchmark).
-export([start/1, loop/4]).

-import(statistics).
-import(ring).

start(Statistics) ->
    spawn(benchmark, loop, [Statistics, dict:new(), 1, 1]).

loop(Statistics, Rings, TokenID, NextRingID) ->
    receive
        list_rings ->
            io:format("Available rings: ~w\n", [dict:fetch_keys(Rings)]),
            loop(Statistics, Rings, TokenID, NextRingID);

        {token, _, undefined, undefined} ->
            io:format("Error: you must define something!\n"),
            loop(Statistics, Rings, TokenID, NextRingID);

        {token, RingID, Steps, undefined} ->
            case dict:find(RingID, Rings) of
                {ok, Ring} -> Ring ! {TokenID, Steps, undefined};                    
                error -> io:format("Error: no such ring\n")
            end,
            loop(Statistics, Rings, TokenID + 1, NextRingID);

        {token, RingID, Steps, Seconds} -> 
            case dict:find(RingID, Rings) of
                {ok, Ring} ->
                    {MegaSec, Sec, Milisec} = now(),
                    StopTime = {MegaSec + ((Sec + Seconds) div 1000000),
                        (Sec + Seconds) rem 1000000, Milisec},
                    Ring ! {TokenID, Steps, StopTime};
                error -> io:format("Error: no such ring\n")
            end,
            loop(Statistics, Rings, TokenID + 1, NextRingID);

        {start, Size} ->
            NewRing = ring:start(NextRingID, self(), Statistics, Size),
            receive 
                {ring, created, NextRingID} ->
                    io:format("Ring ~w created with size: ~w\n", 
                        [NextRingID, Size]),
                    loop(Statistics, dict:store(NextRingID, NewRing, Rings),
                            TokenID, NextRingID + 1)
            after
                3000 -> 
                    io:format("Ring ~w timeout!\n", [NextRingID]),
                    NewRing ! stop,
                    loop(Statistics, Rings, TokenID, NextRingID)
            end;
            
        {stop, RingID} ->
            case dict:find(RingID, Rings) of
                {ok, Ring} ->
                    Ring ! stop,
                    receive
                        {ring, destroyed, RingID} ->
                            io:format("Ring ~w destroyed\n", [RingID])
                    after
                        3000 ->
                            io:format("Ring ~w timeout!\n", [RingID])
                    end,
                    loop(Statistics, dict:erase(RingID, Rings), TokenID, NextRingID);

                error ->
                    io:format("Error: no such ring\n"),
                    loop(Statistics, Rings, TokenID, NextRingID)
            end;

        stop ->
            lists:map(fun({_, Ring}) -> Ring ! stop end, dict:to_list(Rings))
    end.
