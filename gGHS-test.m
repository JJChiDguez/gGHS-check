clear;
P <x >:= PolynomialRing ( GF (2) );

F1 <v >:= ext < GF (2) | x ^127 + x ^63 + 1 >;
F2 <U >:= ext < GF (2) | x ^2 + x + 1 >;
F3 := GF (2) ;

K1 <u >:= ext < F1 | x ^2 + x + 1 >;
K2 <V >:= ext < F2 | x ^127 + x ^63 + 1 >;
K3 <W >:= ext < GF (2) | x ^254 + x ^7 + x ^2 + x + 1 >;

Embed (K1 , K2 );
Embed (K2 , K3 );
Embed (K3 , K1 );

n := 127;
d := 7;

P1 < y01 >:= PolynomialRing ( K1 );
P2 < y02 >:= PolynomialRing ( K2 );
P3 < y03 >:= PolynomialRing ( K3 );

fact0x00 := Factorisation (x ^n + 1) ;
fact := [];
for jj in [1 .. # fact0x00 ] do
	fact [ jj ]:= fact0x00 [jj ,1];
end for;

frob01 := map < P2 -> P2 | z :-> z ^# F2 >;
frob02 := map < P3 -> P3 | z :-> z ^# F3 >;

f01 := MultiplyFrobenius ( y02 , fact [2] , frob01 );
f02 := MultiplyFrobenius ( y03 , fact [2] , frob02 );


AlgVul := function ( var_b , var_S , var , var_frob , var_PolyRing )
	beta := Sqrt ( var_b );
	au0x01 := var_PolyRing !1;
	jj := 0;
	while ( ( au0x01 eq var_PolyRing !1) and ( jj lt # var_S ) ) do
		jj := jj + 1;
		var_s1 := MultiplyFrobenius ( var , var_S [ jj ,1] , var_frob );
		b_jj := Evaluate ( var_s1 , beta * var ) div ( beta ^( Degree ( var_s1 ))* var );
		var_s2 := MultiplyFrobenius ( var , var_S [ jj ,2] , var_frob );
		sp_jj := Polynomial ( Reverse ( Coefficients ( var_s2 ))) ;
		au0x01 := GCD ( b_jj , sp_jj );
	end while ;
	if( au0x01 ne var_PolyRing !1) then return jj , true ; else return 0, false ; end if;
end function ;


S_F4 :=[];
S_F2 :=[];
for ii in [2 .. # fact ] do
	Append (~ S_F4 ,[ fact [ ii ],x +1]) ;
	Append (~ S_F4 ,[ fact [ ii ], fact [ ii ]]) ;
	Append (~ S_F4 ,[( x +1) * fact [ ii ],x +1]) ;
	Append (~ S_F4 ,[( x +1) * fact [ ii ], fact [ ii ]]) ;
	Append (~ S_F4 ,[( x +1) * fact [ ii ] ,( x +1) * fact [ ii ]]) ;

	Append (~ S_F2 ,[ fact [ ii ],x ^2+1]) ;
	Append (~ S_F2 ,[( x +1) * fact [ ii ],x ^2+1]) ;
	Append (~ S_F2 ,[( x ^2+1) * fact [ ii ] ,x +1]) ;
	Append (~ S_F2 ,[( x ^2+1) * fact [ ii ] ,x ^2+1]) ;
	Append (~ S_F2 ,[( x ^2+1) * fact [ ii ] , fact [ ii ]]) ;
	Append (~ S_F2 ,[( x ^2+1) * fact [ ii ] ,( x +1) * fact [ ii ]]) ;
	Append (~ S_F2 ,[( x ^2+1) * fact [ ii ] ,( x ^2+1) * fact [ ii ]]) ;
end for ;


bK1 := K1 !( F1 ! IntegerToSequence (0x59C8202CB9E6E0AE2E6D944FA54DE7E5 ,2) );
bK2 := K2 ! bK1 ;
bK3 := K3 ! bK2 ;

aK1 := K1 !u;
aK2 := F2 ! aK1 ;
aK3 := K3 ! aK2 ;

EK1 := EllipticCurve ([ K1 | K1 !1 , aK1 , 0, 0, bK1 ]) ;
EK2 := EllipticCurve ([ K2 | K2 !1 , aK2 , 0, 0, bK2 ]) ;
EK3 := EllipticCurve ([ K3 | K3 !1 , aK3 , 0, 0, bK3 ]) ;

r1 := FactoredOrder ( EK1 ) ;
r2 := FactoredOrder ( EK2 ) ;
r3 := FactoredOrder ( EK2 ) ;

print "E is an " , EK1 ;
assert r1 eq r2;
assert r1 eq r3;
print "of order: ", r3:Hex;

print "\n";
Ti0 := Cputime () ;
i01 , it01 := AlgVul ( bK3 , S_F2 , y03 , frob02 , P3 );
Tf0 := Cputime () ;
print "Is E vulnerable over F_ {2^{254}}? ->" , it01 ;
print "The total time for answering the vulnerability over F_ {2^{254}} was " ,Tf0 - Ti0, " seconds" ;

Ti1 := Cputime () ;
i02 , it02 := AlgVul ( bK2 , S_F4 , y02 , frob01 , P2 );
Tf1 := Cputime () ;
print "Is E vulnerable over F_ {{2^{2}}^{127}}? ->" , it02 ;
print "The total time for answering the vulnerability over F_ {{2^{2}}^{127}} was " , Tf1 - Ti1, " seconds" ;

exit;
