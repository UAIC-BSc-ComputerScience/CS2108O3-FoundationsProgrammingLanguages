nat(0).
nat(s(N)) :- nat(N).


even(0).
even(s(s(N))) :- even(N).



appetizer(guacamole, 2).
appetizer(ceapa, 1).

meat(beef, 13).
meat(pork, 15).
meat(fish, 6).

desert(icecream, 8).
desert(cake, 10).


lightmeal(A,A1,M,D) :- appetizer(A, KA), appetizer(A1, KA1), meat(M, KM), desert(D, KD), 0 < KA, KA1 > 0, KM > 0, KD > 0, KA + KA1 + KM + KD < 20.
