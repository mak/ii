-module(ring).
-export([start/4, create_ring/4, loop/5]).


start(RingID, Svisor, Stats, Size) 
when is_pid(Svisor), is_pid(Stats), is_integer(Size),Size > 0 ->
    spawn(ring, create_ring, [RingID, Svisor, Stats, Size]).


create_ring(RingID, Svisor, Stats, Size) -> 
    Stats ! {ring, start, RingID, Size, now()},

    Last = create_ring(RingID, Svisor, Stats, Size - 1, self()),

    Stats ! {ring, stop, RingID, Size, now()},
    Svisor ! {ring, created, RingID},
    
    loop(RingID, 0, Last, Svisor, Stats).


create_ring(_, _, _, 0, Next) -> Next;
create_ring(RingID, Svisor, Stats, Size, Next) ->
    create_ring(RingID, Svisor, Stats, Size - 1, 
        spawn(ring, loop, [RingID, Size, Next, Svisor, Stats])).


loop(RingID, N, Next, Svisor, Statistics) 
when is_pid(Next), is_pid(Statistics), is_pid(Svisor) ->
    receive 
        stop ->
            io:format("Ring ~w: stopping\n", [RingID]),
            Next ! stop_no_wait,
            receive
                stop_no_wait ->
                    io:format("Ring ~w: stopped\n", [RingID]),
                    Svisor ! {ring, destroyed, RingID}
            end;

        stop_no_wait ->
            Next ! stop_no_wait;

        {TokenID, MaxSteps, StopTime} ->
            Statistics ! {token, start, TokenID, MaxSteps, now()},
            self() ! {TokenID, 0, MaxSteps, StopTime},
            loop(RingID, N, Next, Svisor, Statistics);

        {TokenID, MaxSteps, MaxSteps, _} ->
            Statistics ! {token, stop, TokenID, MaxSteps, N, now()},
            loop(RingID, N, Next, Svisor, Statistics);

        {TokenID, Steps, MaxSteps, undefined} ->
            Next ! {TokenID, Steps + 1, MaxSteps, undefined},
            loop(RingID, N, Next, Svisor, Statistics);

        {TokenID, Steps, undefined, StopTime} ->
            case timer:now_diff(StopTime, now()) of
                Diff when Diff > 0 ->
                    Next ! {TokenID, Steps + 1, undefined, StopTime};
                Diff when Diff =< 0 ->
                    Statistics ! {token, stop, TokenID, Steps, N, now()}
            end,
            loop(RingID, N, Next, Svisor, Statistics);

        {TokenID, Steps, MaxSteps, StopTime} ->
            case timer:now_diff(StopTime, now()) of
                Diff when Diff > 0 ->
                    Next ! {TokenID, Steps + 1, MaxSteps, StopTime};
                Diff when Diff =< 0 ->
                    Statistics ! {token, stop, TokenID, Steps, N, now()}
            end,
            loop(RingID, N, Next, Svisor, Statistics)
    end.
