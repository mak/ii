-module(statistics).
-export([start/0, loop/2]).

-record(token, {startTime, stopTime, steps, maxSteps, ring, processNum}).
-record(ring, {startTime, stopTime, size}).

start() ->
    spawn(statistics, loop, [dict:new(), dict:new()]).

loop(Rings, Tokens) ->
    receive
        stop -> io:format("Statistics stopped\n");

        {ring, report} ->
            F = fun(RingID) -> 
                    Ring = dict:fetch(RingID, Rings),
                    io:format("Ring ~w created in ~w ms\n", 
                        [RingID, timer:now_diff(Ring#ring.stopTime, 
                         Ring#ring.startTime)])
                end,
            lists:map(F, dict:fetch_keys(Rings)),
            loop(Rings, Tokens);

        {ring, start, RingID, Size, StartTime} ->
            loop(dict:store(RingID, #ring{startTime = StartTime, size = Size},
                    Rings), Tokens);

        {ring, stop, RingID, StopTime} ->
            case dict:find(RingID, Rings) of
                {ok, Ring} ->
                    loop(dict:store(RingID, Ring#ring{stopTime = StopTime},
                            Rings), Tokens);

                error ->
                    io:format("Statistics: no such ring!\n"),
                    loop(Rings, Tokens)
            end;
    
        {token, report} ->
            F = fun(TokenID) ->
                    Token = dict:fetch(TokenID, Tokens),
                    io:format("Token ~w done ~w steps in ~w ms in ring: ~w\n", 
                        [TokenID, Token#token.steps, timer:now_diff(Token#token.stopTime,
                        Token#token.startTime), Token#token.ring])
                end,
            lists:map(F, dict:fetch_keys(Tokens)),
            loop(Rings, Tokens);

        {token, start, TokenID, RingID, MaxSteps, StartTime} ->
            loop(Rings, dict:store(TokenID, #token{maxSteps = MaxSteps,
                    ring = RingID, startTime = StartTime}, Tokens));

        {token, stop, TokenID, Steps, N, StopTime} ->
            case dict:find(TokenID, Tokens) of
                {ok, Token} ->
                    loop(Rings, dict:store(TokenID, Token#token{steps = Steps,
                        stopTime = StopTime, processNum = N},Tokens));

                error ->
                    io:format("Statistics: no such token!\n"),
                    loop(Rings, Tokens)
            end;
           
        Msg -> 
            io:format("Statistics received: ~w~n", 
                [Msg]),
            loop(Rings, Tokens)
    end.
