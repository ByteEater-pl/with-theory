dziecko(jan, anna).
dziecko(ewa, anna).
dziecko(anna, tomasz).
dziecko(józef, ewa).
dziecko(tomasz, adrian).
dziecko(tomasz, łucja).

potomek(X, Y) :- dziecko(X, Y).
potomek(X, Y) :- dziecko(X, Z), potomek(Z, Y).

rodzice(jan, [paweł, aneta]).
rodzice(artur, [paweł, julia]).
rodzice(henryk, [julia]).
%member, <, >, ==, /=, @>, length, append/3, append/2, =/2, is, sort – predykaty wbudowane

len([], 0).
len([_|T], N) :- len(T, K), N is K + 1.

member(X, [X|_]).
member(X, [_|T]) :- member(X, T).

join([], L, L).
join([H|T], L, [H|R]) :- join(T, L, R).

min2(X, X, X).
min2(X, Y, X) :- X < Y.
min2(X, Y, Y) :- X > Y.

min([X], X).
min([H|T], X) :-
    min(T, N),
    % źle: (H /> N, X = H; H > N, X = N).
    % /op to konwencja zanegowanych operatorów jednak w Haskellu
    min2(H, N, X).

split_min([X], [[], X, []]).
split_min([A,B|T], [P,X,Q]) :-
    split_min([B|T], [R,Y,S]),
    (A > Y ->
    	[P,X,Q]=[[A|R],Y,S];
    	[P,X,Q]=[[],A,[B|T]]).
/* alternatywnie, bez powtarzania [P,X,Q]
split_min([A,B|T], [P,X,Q]) :-
    split_min([B|T], [R,Y,S]),
    (A > Y ->
    	L=[[A|R],Y,S];
    	L=[[],A,[B|T]]),
    [P,X,Q] = L.
*/

% sortowanie przez proste wybieranie
sortuj([], []).
sortuj(L, [M|T]) :-
    split_min(L, [B,M,A]),
    append(B,A,C),
    sortuj(C,T).
