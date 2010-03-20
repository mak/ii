-module(just).
-export([ljust/2, rjust/2, centre/2]).

ljust(String, Width) -> just(String, Width, left).
rjust(String, Width) -> just(String, Width, right).
centre(String, Width) -> just(String, Width, centre).

just(String, Width, Just) ->
    if
        length(String) > Width -> String;
        true -> shift(String, Width - length(String), Just)
    end.

shift(String, 0, _) -> String;
shift(String, 1, centre) -> " " ++ String;
shift(String, N, Just) when N > 0 ->
    case Just of
        left -> shift(" " ++ String, N - 1, Just);
        right -> shift(String ++ " ", N - 1, Just);
        centre -> shift(" " ++ String ++ " ", N - 2, Just)
    end.
