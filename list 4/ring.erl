-module(ring).
-export([start/3, create_ring/3, loop/3]).


start(Svisor, Stats, Size) 
when is_pid(Svisor), is_pid(Stats), is_integer(Size),Size > 0 ->
    spawn(ring, create_ring, [Svisor, Stats, Size]).


create_ring(Svisor, Stats, Size) -> 
    RingID = 1,
    Stats ! {ring, start, RingID, Size, now()},

    Last = create_ring(Svisor, Stats, Size - 1, self()),

    Stats ! {ring, stop, RingID, Size, now()},
    Svisor ! {ring, created, RingID},
    
    loop(0, Last, Stats).


create_ring(_, _, 0, Next) -> Next;
create_ring(Svisor, Stats, Size, Next) ->
    create_ring(Svisor, Stats, Size - 1, 
        spawn(ring, loop, [Size, Next, Stats])).


loop(N, Next, Statistics) when is_pid(Next), is_pid(Statistics) ->
    io:format("Thread ~w ~w: listening, next is ~w\n", [N, self(),Next]), 
    receive 
        stop ->
            io:format("Thread ~w: stopping\n", [N]),
            Next ! stop;
            
        {TokenID, 0, _} ->
            io:format("Thread ~w received token with 0 steps\n", [N]),
            Statistics ! {token, stop, TokenID, 0, N, now()},
            loop(N, Next, Statistics);

        {TokenID, Steps, StopTime} -> 
            io:format("Thread ~w: received token with steps: ~w\n", [N, Steps]),
            Next ! {TokenID, Steps - 1, StopTime},
            loop(N, Next, Statistics)
    end.
