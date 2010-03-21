#!/usr/bin/env escript

%-module(zadanie2).
%-compile(export_all).

main([]) -> main(["50"]);
main([Width]) -> main([Width, "2"]);
main([Width, Indent]) -> loop(list_to_integer(Width),
                                list_to_integer(Indent)).

loop(Width, Indent) ->
    Par = get_paragraph(),
    if
        Par == eof -> ok;
        Par == "" -> loop(Width, Indent);
        true -> 
            io:format("~s\n\n", [format_paragraph(Par, Width, Indent)]),
            loop(Width, Indent)
    end.

format_paragraph(Par, Width, Indent) -> 
    format(string:tokens(Par, " \n"), Width, Indent, []).

format([], _, _, Lines) -> string:join(lists:reverse(Lines), "\n");

format(Words, Width, Indent, []) ->
    {Line, Rest} = make_line(Words, Width - Indent),
    Indented = lists:duplicate(Indent, 32) ++ Line,
    format(Rest, Width, 0, [Indented]);

format(Words, Width, _, Lines) ->
    {Line, Rest} = make_line(Words, Width),
    if
        Line == "" -> Lines;
        true -> format(Rest, Width, 0, [Line|Lines])
    end.

make_line(Words, Width) ->
    {Taken, Rest} = take_words(Words, Width),
    {fill_to_width(Taken, Width), Rest}.

fill_to_width([], _) -> "";
fill_to_width([Word], _) -> Word;
fill_to_width([Word|Words], Width) -> 
    WordsWidth = lists:foldl(fun(S, X) -> 
                X + length(S) end, length(Word), Words),
    N = (Width - WordsWidth) div (length(Words)),
    M = (Width - WordsWidth) rem (length(Words)),
    if
        M == 0 -> string:join([Word|Words], lists:duplicate(N, 32));
        M > 0  -> Word ++ join(Words, N, M)
    end.

join([], _, _) -> "";

join(Words, N, 0) ->
    lists:duplicate(N, 32) ++ string:join(Words, lists:duplicate(N, 32));

join([Word|Words], N, M) when M > 0 ->
    join([[32|Word]|Words], N, M - 1).

take_words(Words, Width) ->
    take_words(Words, Width, []).

take_words([Word|Words], Width, []) when length(Word) > Width ->
    {[Word], Words};

take_words([Word|Words], Width, Taken) when length(Word) =< Width ->
    take_words(Words, Width - length(Word) - 1, [Word|Taken]);

take_words(Words, _, Taken) -> {lists:reverse(Taken), Words}.

get_line() ->
    Line = io:get_line(""),
    if
        Line == eof -> eof;
        true -> string:strip(string:strip(Line, both, 10), both)
    end.

get_paragraph() -> 
    Line = get_line(),
    if
        Line == eof -> eof;
        true -> get_paragraph(Line)
    end.

get_paragraph(Par) -> 
    Line = get_line(),
    if
        Line == eof -> Par;
        Line == "" -> Par;
        true -> get_paragraph(string:concat(Par, Line))
    end.
