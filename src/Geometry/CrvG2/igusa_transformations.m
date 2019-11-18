//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Transformations between Igusa, Clebsch, and Igusa-Clebsch invariants    //
//    and absolute versions of these invariants                             //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
// These functions concern the following invariants
// Igusa Clebsch Invariants 
//   (I2, I4, I6, I10) = (A', B', C', D') on p. 319 of Mestre
// Clebsch Invariants (A, B, C, D) on p. 317 of Mestre
// Igusa Invariants (J2, J4, J6, J8, J10) 
//////////////////////////////////////////////////////////////////////////////
// The absolute invariants functions (weighted degree zero) 
// are defined in terms of the Igusa-Clebsch variants: 
//   (j1, j2, j3) = (I2^4/I10, I4*I2^3/I10, I6*I2^2/I10)
// are defined in terms of the Clebsch variants: 
//   (i1, i2, i3) = (j1', j2', j3') = (A^5/D, B*A^3/D, C*A^2/D) 
// and finally the Igusa invariants
//   (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)
// as defined below (see p. 325 of Mestre).
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
// Direction: Igusa -> Clebsch -> Igusa-Clebsch 
//////////////////////////////////////////////////////////////////////////////

intrinsic AbsoluteIgusaToClebschInvariants(xx::[RngElt]) -> SeqEnum
    {Convert absolute Igusa invariants (x1,..,x5) to absolute
    Clebsch invariants (i1,i2,i3).}
    // (x1, x2, x3, x4, x5) -> (i1, i2, i3)
    require #xx in {5,10} : "Argument must be a sequence of 5 (or 10) invariants.";
    require IsUnit(Universe(xx)!30) : 
	"The universe of argument must contain inverses of 2, 3, and 5.";
    x1, x2, x3, x4, x5 := Explode(xx);
    return [
	-x1/(15*120^4),
	(-3*x1 + 40*x2)/(22500*120^3),
        (x1 - 20*x2 - 200*x3)/(37500*120^3)
	];
end intrinsic;

intrinsic AbsoluteClebschToIgusaClebschInvariants(ii::[RngElt]) -> SeqEnum
    {Convert absolute Clebsch invariants (i1,i2,i3) to absolute
    Igusa-Clebsch invariants (j1,j2,j3).}
    // (i1, i2, i3) -> (j1, j2, j3)
    require #ii eq 3 : "Argument must be a sequence of 3 invariants.";
    i1, i2, i3 := Explode(ii);
    j1 := -24883200000*i1;
    j2 := 1244160000*i1 - 11664000000*i2;
    j3 := 124416000*i1 - 1555200000*i2 + 2916000000*i3;
    return [ j1, j2, j3 ];
end intrinsic;

intrinsic AbsoluteIgusaToIgusaClebschInvariants(xx::[RngElt]) -> SeqEnum
    {Convert absolute Igusa invariants (x1,..,x5) to absolute
    Igusa-Clebsch invariants (j1,j2,j3,j4).}
    // (x1, x2, x3, x4, x5) -> (j1, j2, j3, j4)
    require #xx in {5,10} :
	"Argument must be a sequence of 5 or 10 invariants.";
    require IsUnit(Universe(xx)!2) : 
	"The universe of argument must contain an inverse of 2.";
    x1, x2, x3, x4, x5 := Explode(xx);
    return [ 8*x1,
	(x1 - 24*x2)/2,
        (x1 - 20*x2 - 72*x3)/8,
	(x1 - 44*x2 + 408*x3 - 1920*x4 + 1728*x5)/128
	];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Direction: Igusa-Clebsch -> Clebsch -> Igusa
//////////////////////////////////////////////////////////////////////////////

intrinsic AbsoluteIgusaClebschToClebschInvariants(jj::[RngElt]) -> SeqEnum
    {Convert absolute Igusa-Clebsch invariants (j1,j2,j3,j4) to absolute
    Clebsch invariants (i1,i2,i3).}
    // (j1, j2, j3, j4) -> (i1, i2, i3)
    require #jj eq 4 : "Argument must be a sequence of 4 invariants.";
    require IsUnit(Universe(jj)!30) : 
	"The universe of argument must contain inverses of 2, 3, and 5.";
    j1, j2, j3 := Explode(jj);
    i1 := -j1/24883200000;
    i2 := (-j1 - 20*j2)/233280000000;
    i3 := (-j1 - 80*j2 + 600*j3)/1749600000000;
    return [ i1, i2, i3 ];
end intrinsic;

intrinsic AbsoluteClebschToIgusaInvariants(ii::[RngElt]) -> SeqEnum
    {Convert absolute Clebsch invariants (i1,i2,i3) to absolute
    Igusa invariants (x1,x2,x3,x4,x5).}
    // (i1, i2, i3) -> (x1, x2, x3, x4, x5)
    require #ii eq 3 : "Argument must be a sequence of 3 invariants.";
    i1, i2, i3 := Explode(ii);
    /*
    // i1 = A^5/Delta, i2 = A^3*B/Delta, i3 = A*C/Delta,
    // and w1 = D/A^5, where
    w1 := (-62208*i1^2 + 972000*i1*i2 + 1620000*i1*i3 - i1
	- 3037500*i2^2 - 6075000*i2*i3)*u1^2/4556250;
    */
    bool, u1 := IsInvertible(i1);
    require bool : "Argument must have invertible first element.";
    x1 := -3110400000*i1;
    x2 := -38880000*(6*i1 - 25*i2);
    x3 := 1296000*(6*i1 - 75*i2 - 250*i3);
    x4 := 4050*(156*i1^2 - 1500*i1*i2 - 2000*i1*i3 + 1875*i2^2)*u1;
    x5 := 16200*(6*i1 - 75*i2 - 250*i3)*(6*i1 - 25*i2)*u1;
    return [ x1, x2, x3, x4, x5 ];
end intrinsic;

intrinsic AbsoluteIgusaClebschToIgusaInvariants(jj::[RngElt]) -> SeqEnum
    {Convert absolute Igusa-Clebsch invariants (j1,j2,j3) to absolute
    Igusa invariants (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10).}
    // (j1, j2, j3, j4) -> (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)
    require #jj eq 4 : "Argument must be a sequence of 4 invariants.";
    j1, j2, j3, j4 := Explode(jj);
    bool, u1 := IsInvertible(j1);
    require bool : "Argument must have invertible first element.";
    // j1 = I2^5/I10, j2 = I4*I2^3/I10, j3 = I6*I2^2/I10, j4 := I4*I6/I10 = j2*j3/j1
    return IgusaToAbsoluteIgusaInvariants(
	IgusaClebschToIgusaInvariants([1,j2*u1,j3*u1,u1]));
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// 'Absolute' weight zero invariants from weighted invariants 
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaClebschToAbsoluteIgusaClebschInvariants(II::[RngElt]) -> SeqEnum
    {Absolute Igusa-Clebsch invariants (j1,j2,j3) =
    (I2^5/I10, I4*I2^3/I10, I6*I2^2/I10, I4*I6/I10) from Igusa-Clebsch
    invariants (I2,I4,I6,I10).}
    // (I2, I4, I6, I10) ->
    //   (j1, j2, j3) = (I2^5/I10, I4*I2^3/I10, I6*I2^2/I10)
    require #II eq 4 : "Argument must be a sequence of 4 invariants.";
    I2, I4, I6, I10 := Explode(II);
    bool, U := IsInvertible(I10);
    require bool : "Argument element 4 must be invertible."; 
    return [ I2^5*U, I4*I2^3*U, I6*I2^2*U, I4*I6*U ];
end intrinsic;

intrinsic ClebschToAbsoluteClebschInvariants(ABCD::[RngElt]) -> SeqEnum
    {Absolute Clebsch invariants (i1,i2,i3) =
    (A^5/Delta, B*A^3/Delta, C*A^2/Delta) from Clebsch invariants
    (A,B,C,D).}
    // (A, B, C, D) -> (i1, i2, i3) = (A^5/D, B*A^3/D, C*A^2/D)
    require #ABCD eq 4 : "Argument must be a sequence of 4 invariants.";
    A, B, C, D := Explode(ABCD);
    Delta := -62208*A^5 + 972000*A^3*B + 1620000*A^2*C
	- 3037500*A*B^2 - 6075000*B*C - 4556250*D;
    bool, U := IsInvertible(Delta);
    require bool : "Argument element 4 must be invertible."; 
    return [ A^5*U, B*A^3*U, C*A^2*U ];
end intrinsic;

intrinsic IgusaToAbsoluteIgusaInvariants(JJ::[RngElt] : Short := false) -> SeqEnum
    {Absolute Igusa invariants (x1,x2,x3,x4,x5) =
    (J2^5/J10, J4*J2^3/J10, J6*J2^2/J10, J8*J2/J10, J4*J6/J10)
    from Igusa invariants (J2,J4,J6,J8,J10).}
    // (J2, J4, J6, J8, J10) -> (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)
    require #JJ eq 5 : "Argument must be a sequence of 5 invariants.";
    J2, J4, J6, J8, J10 := Explode(JJ);
    bool, U := IsInvertible(J10);
    require bool : "Argument element 5 must be invertible.";
    x1 := J2^5*U;
    x2 := J4*J2^3*U;
    x3 := J6*J2^2*U;
    x4 := J8*J2*U;
    x5 := J4*J6*U;
    if Short then
	return [ x1, x2, x3, x4, x5 ];
    end if;
    x6 := J4*J8^2*U^2;
    x7 := J6^2*J8*U^2;
    x8 := J6^5*U^3;
    x9 := J6*J8^3*U^3;
    x10 := J8^5*U^4;
    return [ x1, x2, x3, x4, x5, x6, x7, x8, x9, x10 ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Rational conversions: Igusa-Clebsch -> Clebsch -> Igusa
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaClebschToClebschInvariants(II::[RngElt]) -> SeqEnum
    {Convert Igusa-Clebsch invariants to Clebsch invariants.}
    require #II eq 4 : "Argument must be a sequence of 4 invariants.";
    require IsUnit(Universe(II)!30) :
	"The universe of argument must contain inverses of 2, 3, and 5.";
    I2, I4, I6, I10 := Explode(II);
    A := -I2/120;
    B := I4/6750 + 8*A^2/75;
    C := I6/202500 - A*(16*A^2 - 200*B)/375;
    D := -I10/4556250 - 128*A^5/9375
        + (A^2*(48*A*B + 80*C) - B*(150*A*B + 300*C))/225;
    return [ A, B, C, D ];
end intrinsic;

intrinsic IgusaClebschToIgusaInvariants(II::[RngElt]) -> SeqEnum
    {Convert Igusa-Clebsch invariants to Igusa invariants.}
    // (A, B, C, D) -> (J2, J4, J6, J8, J10)
    require #II eq 4 : "Argument must be a sequence of 4 invariants.";
    require IsUnit(Universe(II)!6) :
	"2 and 3 must be invertible in the universe of argument";
    I2, I4, I6, I10 := Explode(II);
    J2  := I2/8;
    J4  := (4*J2^2 - I4)/96;
    J6  := (8*J2^3 - 160*J2*J4 - I6)/576;
    J8  := (J2*J6 - J4^2)/4;
    J10 := I10/4096;
    return [ J2, J4, J6, J8, J10 ];
end intrinsic;

intrinsic ClebschToIgusaInvariants(ABCD::[RngElt]) -> SeqEnum
    {Convert Clebsch invariants to Igusa invariants.}
    // (A, B, C, D) -> (J2, J4, J6, J8, J10)
    require #ABCD eq 4 : "Argument must be a sequence of 4 invariants.";
    require IsUnit(Universe(ABCD)!2) :
	"The universe of argument must contain an inverse of 2.";
    A, B, C, D := Explode(ABCD);
    J2 := -15*A;
    J4 := (270*A^2 - 1125*B)/16;
    J6 := (270*A^3 - 3375*A*B - 11250*C)/32;
    J8 := (-105300*A^4 + 1012500*A^2*B + 1350000*A*C - 1265625*B^2)/1024;
    J10 := (-31104*A^5 + 486000*A^3*B + 810000*A^2*C - 1518750*A*B^2 -
	    3037500*B*C - 2278125*D)/2048;
    return [ J2, J4, J6, J8, J10 ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Integral conversions: Igusa -> Igusa-Clebsch -> Clebsch 
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaToIgusaClebschInvariants(JJ::[RngElt]) -> SeqEnum
    {Convert Igusa invariants to Igusa-Clebsch invariants.}
    // (J2, J4, J6, J8, J10) -> (A, B, C, D)
    require #JJ eq 5 : "Argument must be a sequence of 5 invariants.";
    J2, J4, J6, J8, J10 := Explode(JJ);
    I2 := 8*J2;
    I4 := 4*(J2^2 - 24*J4);
    I6 := 8*(J2*(J2^2 - 20*J4) - 72*J6);
    I10:= 4096*J10;
    return [ I2, I4, I6, I10 ];
end intrinsic;

intrinsic ClebschToIgusaClebschInvariants(ABCD::[RngElt]) -> SeqEnum
    {Convert Clebsch invariants to Igusa-Clebsch invariants.}
    require #ABCD eq 4 : "Argument must be a sequence of 4 invariants.";
    A, B, C, D := Explode(ABCD);
    I2 := -120*A;
    I4 := -720*A^2 + 6750*B;
    I6 := 8640*A^3 - 108000*A*B + 202500*C;
    I10 := -62208*A^5 + 972000*A^3*B + 1620000*A^2*C
	- 3037500*A*B^2	- 6075000*B*C - 4556250*D;
    return [ I2, I4, I6, I10 ];
end intrinsic;

intrinsic IgusaToClebschInvariants(JJ::[RngElt]) -> SeqEnum
    {Convert Igusa invariants to Clebsch invariants.}
    // (J2, J4, J6, J8, J10) -> (A, B, C, D)
    require #JJ eq 5 : "Argument must be a sequence of 5 invariants.";
    J2, J4, J6, J8, J10 := Explode(JJ);
    require IsUnit(Universe(JJ)!15) :
	"3 and 5 must be invertible in the universe of argument";
    A := -J2/15;
    B := (6*J2^2 - 80*J4)/5625;
    C := (2*J2^3 - 40*J2*J4 - 400*J6)/140625;
    D := (24*J2^5 - 1600*J2^3*J4 - 3200*J2^2*J6 + 25600*J2*J4^2
	- 384000*J4*J6 - 6400000*J10)/7119140625;
    return [ A, B, C, D ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
