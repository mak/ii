#!/usr/bin/env escript

-module(zadanie1).
-compile(export_all).

main([]) ->
    loop().


loop() -> 
    Bytes = read_ip_version(),
    io:format("Read: ~w\n", [Bytes]).


read_ip_version() -> 
    [Byte] = read_bytes(1),
    <<Version:4, HeaderLength:4>> = <<Byte>>,
    [ToS] = read_bytes(1),
    TotalLength = bytes_to_integer(read_bytes(2)),
    Identification = bytes_to_integer(read_bytes(2)),
    Flags = bytes_to_integer(read_bytes(2)),
    [TTL] = read_bytes(1),
    [Protocol] = read_bytes(1),
    Checksum = bytes_to_integer(read_bytes(2)),
    SrcIP = read_bytes(4),
    DestIP = read_bytes(4),
    Additional = read_bytes(4 * HeaderLength - 20),
    Data = read_bytes(TotalLength - 4 * HeaderLength),
    {Version, HeaderLength, ToS, TotalLength, Identification, Flags,
     TTL, Protocol, Checksum, SrcIP, DestIP, Additional, Data}.
    

is_hex_digit(D) ->
    (D >= "0") and (D =< "9")
    or
    (D >= "a") and (D =< "f")
    or
    (D >= "A") and (D =< "F").

hex_to_integer("a") -> 10;
hex_to_integer("b") -> 11;
hex_to_integer("c") -> 12;
hex_to_integer("d") -> 13;
hex_to_integer("e") -> 14;
hex_to_integer("f") -> 15;
hex_to_integer("A") -> 10;
hex_to_integer("B") -> 11;
hex_to_integer("C") -> 12;
hex_to_integer("D") -> 13;
hex_to_integer("E") -> 14;
hex_to_integer("F") -> 15;
hex_to_integer([N]) -> [Zero] = "0", N - Zero.

read_bytes(0) -> [];
read_bytes(N) when N > 0 ->
    case io:fread("", "~c~c") of
        {ok, Chars} ->
            case lists:all(fun(D) -> is_hex_digit(D) end, Chars) of
                true  -> 
                    [A, B] = Chars,
                    Byte = hex_to_integer(A)*16 + hex_to_integer(B),
                    [Byte | read_bytes(N - 1)];
                false -> input_error
            end;
        true -> read_error
    end.
   
bytes_to_integer(Bytes) -> 
    lists:foldl(fun(X, A) -> 256 * A + X end, 0, Bytes).
