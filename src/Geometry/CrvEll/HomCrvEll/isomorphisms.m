////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         ELLIPTIC CURVE                             //
//                  ISOMORPHISMS AND TRANSFORMATIONS                  //
//                        by David Kohel 2000                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Transformation(E::CrvEll,T::[RngElt]) -> CrvEll, Map
    {Given an elliptic curve, and a transformation sequence
    T = [r,s,t,u], returns the codomain curve under the
    transformation defined by T.}
    val, T := CanChangeUniverse(T,BaseRing(E));
    require val : "Arguments not defined over compatible rings"; 
    require #T eq 4 : "Argument 2 must have length 4";
    a1,a2,a3,a4,a6 := Explode(aInvariants(E));
    r,s,t,u := Explode(T);
    require IsUnit(u) : "Invalid transformation sequence";
    S := [
      a1*u - 2*s,
      a1*s*u + a2*u^2 - 3*r - s^2,
      -a1*r*u + a3*u^3 + 2*r*s - 2*t,
      -2*a1*r*s*u + a1*t*u - 2*a2*r*u^2 + a3*s*u^3 + a4*u^4 + 3*r^2
          + 2*r*s^2 - 2*s*t,
      a1*r^2*s*u - a1*r*t*u + a2*r^2*u^2 - a3*r*s*u^3 + a3*t*u^3 - 
          a4*r*u^4 + a6*u^6 - r^3 - r^2*s^2 + 2*r*s*t - t^2
    ];
    val, F := IsEllipticCurve(S);
    require val :
	"Argument 2 does not define an elliptic curve tranformation";
    return F, Isomorphism(E,F,T);
end intrinsic;

intrinsic Transformation(S::[RngElt],T::[RngElt]) -> SeqEnum
    {Given a sequence of defining coefficients S = [a1,a2,a3,a4,a6]
    for an elliptic curve, and a transformation sequence T = [r,s,t,u],
    returns the sequence of coefficients of the codomain curves under
    the transformation.}
    if Type(Universe(T)) eq RngInt then
	ChangeUniverse(~T,RationalField());
    end if;
    val, S := CanChangeUniverse(S,Universe(T));
    require val : "Arguments not defined over compatible rings"; 
    require #T eq 4 : "Argument 2 must have length 4";
    a1,a2,a3,a4,a6 := Explode(S);
    r,s,t,u := Explode(T);
    require IsUnit(u) : "Invalid transformation sequence";
    return [
      a1*u - 2*s,
      a1*s*u + a2*u^2 - 3*r - s^2,
      -a1*r*u + a3*u^3 + 2*r*s - 2*t,
      -2*a1*r*s*u + a1*t*u - 2*a2*r*u^2 + a3*s*u^3 + a4*u^4 + 3*r^2
          + 2*r*s^2 - 2*s*t,
      a1*r^2*s*u - a1*r*t*u + a2*r^2*u^2 - a3*r*s*u^3 + a3*t*u^3 - 
          a4*r*u^4 + a6*u^6 - r^3 - r^2*s^2 + 2*r*s*t - t^2
    ];
end intrinsic;

intrinsic InverseTransformation(T::[RngElt]) -> SeqEnum
    {Given a transformation sequence T = [r,s,t,u],
    returns the sequence for the inverse transformation.}
    require #T eq 4 : "Argument 2 must have length 4";
    if Type(Universe(T)) eq RngInt then
	ChangeUniverse(~T,RationalField());
    end if;
    r,s,t,u := Explode(T);
    require IsUnit(u) : "Invalid transformation sequence";
    return [-c^2*r,-c*s,c^3*(r*s-t),c] where c := u^-1;
end intrinsic;

/*
CHARACTERISTIC 2.

> S := [a1,a2,a3,a4,a6];
> a1,_,a3 := Explode(S);
> S1 := Transformation(S,[a3/a1,0,0,1]);
> // _,_,_,new_a4 := Explode(S1);
> new_a4 := a4 + a3^2/a1^2;
> S2 := Transformation(S1,[0,0,new_a4/a1,1]);
> S2;
[
    a1,
    (a1*a2 + a3)/a1,
    0,
    0,
    (a1^6*a6 + a1^5*a3*a4 + a1^4*a2*a3^2 + a1^4*a4^2 + a1^3*a3^3 
        + a3^4)/a1^6
]
y^2 + a1*x*y + (a1*a2 + a3)/a1*x^2 = x^3 + Disc/a1^6

CHARACTERISTIC 3.

> S := [a1,a2,a3,a4,a6];
> a1,_,a3 := Explode(S);
> S1 := Transformation(S,[a3/a1,0,0,1]);
> S2 := Transformation(S1,[0,a1/2,0,1]);  
> S3 := Transformation(S2,[-(a1*a4 + a2*a3)/(a1*(a1^2 + a2)),0,0,1]);  
> S3;
[
    0,
    a1^2 + a2,
    0,
    0,
    (a1^6*a6 + 2*a1^5*a3*a4 + a1^4*a2*a3^2 + 2*a1^4*a4^2 +
    a1^3*a2*a3*a4 + 2*a1^3*a3^3 + 2*a1^2*a2^2*a3^2 +
    a1^2*a2*a4^2 + 2*a1*a2^2*a3*a4 + 
    a2^3*a3^2 + a2^3*a6 + 2*a2^2*a4^2 + a4^3)/(a1^6 + a2^3)
]

y^2 - (a1^2+a2)*x^2 = x^3 + Disc/(a1^6+a2^3)
y^2 - b2*x^2 = x^3 - Disc/b2^3

CHARACTERISTIC > 5.

> S := [a1,a2,a3,a4,a6];
> a1,_,a3 := Explode(S);
> S1 := Transformation(S,[a3/a1,0,0,1]);
> S2 := Transformation(S1,[0,a1/2,0,1]);  

TRANSFORMATIONS.

> T1 := [r,s,t,u]; 
> Transformation([a1,a2,a3,a4,a6],[r,s,t,u]);
[
    (a1 + 2*s)/u,
    (-a1*s + a2 + 3*r - s^2)/u^2,
    (a1*r + a3 + 2*t)/u^3,
    (-a1*r*s - a1*t + 2*a2*r - a3*s + a4 + 3*r^2 - 2*s*t)/u^4,
    (-a1*r*t + a2*r^2 - a3*t + a4*r + a6 + r^3 - t^2)/u^6
]
> T2 := [-r/u^2,-s/u,(r*s-t)/u^3,1/u];
> Transformation($1,T2);
[
  a1,
  a2,
  a3,
  a4,
  a6
]
> Transformation([a1,a2,a3,a4,a6],T2);
[
    a1*u - 2*s,
    a1*s*u + a2*u^2 - 3*r - s^2,
    -a1*r*u + a3*u^3 + 2*r*s - 2*t,
    -2*a1*r*s*u + a1*t*u - 2*a2*r*u^2 + a3*s*u^3 + a4*u^4 + 3*r^2
        + 2*r*s^2 - 2*s*t,
    a1*r^2*s*u - a1*r*t*u + a2*r^2*u^2 - a3*r*s*u^3 + a3*t*u^3 - 
        a4*r*u^4 + a6*u^6 - r^3 - r^2*s^2 + 2*r*s*t - t^2
]
u1 := u^-1;    
T1 := [
      u1*(a1 + 2*s),
      u1^2*(-a1*s + a2 + 3*r - s^2),
      u1^3*(a1*r + a3 + 2*t),
      u1^4*(-a1*r*s - a1*t + 2*a2*r - a3*s + a4 + 3*r^2 - 2*s*t),
      u1^6*(-a1*r*t + a2*r^2 - a3*t + a4*r + a6 + r^3 - t^2) 
   ];
> Transformation($1,T1);
[
  a1,
  a2,
  a3,
  a4,
  a6
]
*/

