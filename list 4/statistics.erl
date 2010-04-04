-module(statistics).
-export([start/0]).

start() ->
    spawn(fun loop/0).

loop() ->
    receive
        stop -> io:format("Statistics stopped\n");
        Msg -> 
            io:format("Statistics received: ~w~n", 
                [Msg]),
            loop()
    end.
