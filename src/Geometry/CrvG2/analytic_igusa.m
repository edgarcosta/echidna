//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
See Mumford, Theta II, Lemma 3.5.6 p.86, and formula 20 in "Equations for the
Jacobian of a hyperelliptic curve".  I've specialised the Rosenhain invariants
to genus 2, called Genus2RosehnainInvariants; see "Higher dimensional 3-adic CM
construction", Carls, Kohel, and Lubicz, and Mumford, Theta II, p.120.

Since the function InternalTheta for chars [[i,j],[k,l]] is too slow if we
don't have k = l = 0, so I avoid these theta values, and calculate mu by
extracting one square root to produce the Rosenhain invariants.
*/

/*
// For reference, van Wamelen computes Rosenhain invariants as follows for
// arbitrary genus (= dimension):

function eta1(g,j)
    // -1 will stand for infinity
    ans := Matrix(RationalField(),2*g,1,[]);
    if j eq -1 then
	return ans;
    end if;
    if j mod 2 eq 1 then
	i := (j+1) div 2;
	ans[i,1] := 1/2;
	for k := g+1 to g+i-1 do
	    ans[k,1] := 1/2;
	end for;
	return ans;
    else
	i := j div 2;
	ans[i,1] := 1/2;
	for k := g+1 to g+i do
	    ans[k,1] := 1/2;
	end for;
	return ans;
    end if;
end function;

function eta(g,S)
    return S eq {} select eta1(g,-1) else &+[ eta1(g,j) : j in S ];
end function;

function etamod1(g,S)
    return Matrix(RationalField(),2*g,1,[((IntegerRing()!(2*e)) mod 2)/2 : e in Eltseq(eta(g,S))]);
end function;

function RosenhainInvariants(tau)
    // Given a small period matrix cooresponding to an analytic Jacobian, A,
    // of genus g this returns a set of 2g-1 complex numbers such that the
    // hyperelliptic curve y^2 = x(x-1) prod (x-s) for s in S has Jacobian
    // isomorphic to A.
    // TODO: This is specialised to g = 2
    CC := BaseRing(tau);
    g := 2;
    V0 := {2..4};
    U := {2*i+1 : i in [0..g]};
    // Compute all characteristics that will be needed
    charlst := {};
    for j in [3..5] do
	if j in V0 then
	    V := V0;
	else
	    V := V0 sdiff {3,j};
	end if;
	UV := U sdiff V;
	Include(~charlst,etamod1(g,UV sdiff {j,-1}));
	Include(~charlst,etamod1(g,UV sdiff {2,1}));
	Include(~charlst,etamod1(g,UV sdiff {2,-1}));
	Include(~charlst,etamod1(g,UV sdiff {j,1}));
    end for;
    charlst := SetToSequence(charlst);
    // Compute theta nulls
    z := Matrix(CC,2,1,[0,0]);
    X := RMatrixSpace(CC,4,1);
    tyme := Cputime();
    thetalst := [ InternalTheta(X!char,z,tau) : char in charlst ];
    print "Theta null values time:", Cputime(tyme);
    // Compute aj, j := 3..2g+1
    rosenhain := [];
    for j in [3..5] do
	if j in V0 then
	    V := V0;
	else
	    V := V0 sdiff {4,j};
	end if;
	UV := U sdiff V;
	ind1 := Index(charlst,etamod1(g,UV sdiff {j,-1}));
	ind2 := Index(charlst,etamod1(g,UV sdiff {2,1}));
	ind3 := Index(charlst,etamod1(g,UV sdiff {2,-1}));
	ind4 := Index(charlst,etamod1(g,UV sdiff {j,1}));
	// print "ind =", [ind1,ind2,ind3,ind4];
	// Matrix([ Transpose(v) : v in charlst[[ind1,ind2,ind3,ind4]] ]);
	aj := (thetalst[ind1]*thetalst[ind2]/(thetalst[ind3]*thetalst[ind4]))^2;
	Append(~rosenhain,aj);
    end for;
    return rosenhain;
end function;
*/

function Genus2RosenhainInvariants(tau)
    CC := BaseRing(tau);
    charlst := [ RMatrixSpace(CC,4,1) | 
	[0,0,0,0],[0,1/2,0,0],[1/2,0,0,0],[1/2,1/2,0,0] ];
    z := Matrix(CC,2,1,[0,0]);
    thetalst := [ InternalTheta(char,z,tau) : char in charlst ];
    a00, a02, a20, a22 := Explode(thetalst);
    A := a00^2*a20^2 - a02^2*a22^2;
    B := -(a00^4-a02^4+a20^4-a22^4);
    mu := Roots(PolynomialRing(CC)![A,B,A])[1][1];
    return [((a00*a02)/(a20*a22))^2, (a02/a22)^2*mu, (a00/a20)^2*mu ];
end function;


intrinsic RosenhainInvariants(IK::RngOrdIdl, prec::RngIntElt :
    PolarizingElement := 1,
    SymplecticReduction := true,
    PrecisionScalar := 2, // !!! see below
    UseReducedRepresentative := true) -> SeqEnum
    {}
    K := NumberField(Order(IK));
    g := Degree(K) div 2;
    require IsCMField(K) and g eq 2 : "Argument 1 must be a quartic CM field.";
    DAB := QuarticCMFieldInvariants(K);
    if Type(PolarizingElement) in {RngOrdElt,FldNumElt} then
	// Ignoring UseReducedRepresentative, and doing the validity check:
	OK := Order(IK);
	xi := PolarizingElement;
	c := ComplexConjugation(K);
	DK := Different(OK);
	require IK*c(IK)*DK eq ideal< OK | xi > :
	    "Parameter 'PolarizingElement' must generate IK*IK_bar*DK.";
    else
	if UseReducedRepresentative then
	    IK := MinkowskiReduction(IK);
	end if;
	bool, xi := IsPrincipallyPolarizable(IK : Reduction := true);
	require bool : "Argument 1 must be principally polarizable.";
    end if;
    // This is a HUGE inflation factor -- AND it is returned with this precision!
    // (Presumably this is an empirical correction for huge precision loss...)
    CC := ComplexField(PrecisionScalar*prec);
    tau := SmallPeriodMatrix(IK,xi,CC : Reduction := SymplecticReduction, Al := "Wamelen");
    tyme := Cputime();
    EE := Genus2RosenhainInvariants(tau);
    vprint IgusaInvariant : "Rosenhain invariant time:", Cputime(tyme);
    return EE;
end intrinsic;

intrinsic AbsoluteIgusaInvariants(IK::RngOrdIdl, prec::RngIntElt :
    PolarizingElement := 1,
    SymplecticReduction := true,
    PrecisionScalar := 2, // !!! see below
    UseReducedRepresentative := true) -> SeqEnum
    {}
    K := NumberField(Order(IK));
    g := Degree(K) div 2;
    require IsCMField(K) and g eq 2 : "Argument 1 must be a quartic CM field.";
    EE := RosenhainInvariants(IK, prec :
	PolarizingElement := PolarizingElement,
	SymplecticReduction := SymplecticReduction,
	PrecisionScalar := PrecisionScalar, 
	UseReducedRepresentative := UseReducedRepresentative);
    JJ := RosenhainToAbsoluteIgusaInvariants(EE);
    // Note (above) that the return value of Rosenhain invariants doubles 
    // the precision (arbitrarily), and here this precision is dropped:
    return ChangeUniverse(JJ,ComplexField(prec));
end intrinsic;

/*
PQ<x> := PolynomialRing(RationalField());
CM_hyper := [
    x^5 - 1,
    - x^5 + 3*x^4 + 2*x^3 - 6*x^2 - 3*x + 1,
    - 11*x^6 - 2*x^5 - x^4 + 4*x^3 + 7*x^2 - 6*x + 1,
    - 4*x^5 + 30*x^3 - 45*x + 22,
    - 8*x^6 + 52*x^5 - 250*x^3 + 321*x + 131,
    - 8*x^6 - 64*x^5 + 1120*x^4 + 4760*x^3 - 48400*x^2 + 22627*x - 91839,
    79888*x^6 + 293172*x^5 - 348400*x^3 - 29744*x + 103259,
    289*x^6 + 242*x^5 - 225*x^4 - 92*x^3 + 87*x^2 - 42*x - 43,
    - 584*x^6 - 4020*x^5 + 28860*x^4 + 130240*x^3 - 514920*x^2 - 190244*x - 289455,
    - 444408*x^6 + 6986711*x^5 + 44310170*x^4 - 582800*x^3 + 2656360*x^2 - 8866880*x + 2160600,
    - 544*x^6 - 228*x^5 + 168*x^4 + 680*x^3 + 36*x^2 + 396*x - 567,
    8*x^6 - 530*x^5 - 160*x^4 + 64300*x^3 + 265420*x^2 - 529*x,
    - 4116*x^6 + 64582*x^5 - 139790*x^4 - 923200*x^3 - 490750*x^2 + 233309*x + 9347,
    1183*x^6 + 1560*x^5 + 1560*x^4 - 1040*x^3 + 36*x,
    - 10584*x^6 - 5940*x^5 + 18180*x^4 + 3200*x^3 - 18960*x^2 - 6508*x + 3465,
    - 243*x^6 + 2223*x^5 - 1566*x^4 - 19012*x^3 + 903*x^2 + 19041*x - 5882,
    - 70399443*x^6 + 36128207*x^5 + 262678342*x^4 - 48855486*x^3 - 112312588*x^2 + 36312676*x,
    50091*x^6 - 54865*x^5 - 129108*x^4 + 158576*x^3 + 110664*x^2 - 180624*x - 112360,
    - 103615*x^6 - 41271*x^5 + 17574*x^4 + 197944*x^3 + 67608*x^2 - 103680*x - 40824
];
CM_polys := [
    x^4 - 2*x^3 + 4*x^2 - 3*x + 1,
    x^4 + 4*x^2 + 2,
    x^4 - x^3 + 2*x^2 + 4*x + 3,
    x^4 + 10*x^2 + 20,
    x^4 + 10*x^2 + 20,
    x^4 + x^3 + 16*x^2 + 16*x + 61,
    x^4 - 2*x^3 + 34*x^2 - 33*x + 61,
    x^4 + x^3 + 4*x^2 + 20*x + 23,
    x^4 - 2*x^3 + 44*x^2 - 43*x + 101,
    x^4 + x^3 + 21*x^2 + 21*x + 101,
    x^4 - x^3 + 5*x^2 - 7*x + 49,
    x^4 + 20*x^2 + 50,
    x^4 + 20*x^2 + 50,
    x^4 + x^3 + 15*x^2 - 17*x + 29,
    x^4 + x^3 + 15*x^2 - 17*x + 29,
    x^4 + 26*x^2 + 52,
    x^4 + 26*x^2 + 52,
    x^4 + x^3 + 7*x^2 - 43*x + 47,
    x^4 + x^3 + 8*x^2 + 42*x + 117
    ];
C1_polys := [
    x^4 - 2*x^3 + 4*x^2 - 3*x + 1,
    x^4 + 4*x^2 + 2,
    x^4 - x^3 + 2*x^2 + 4*x + 3,
    x^4 + x^3 + 4*x^2 + 20*x + 23,
    x^4 - x^3 + 5*x^2 - 7*x + 49,
    x^4 + x^3 + 7*x^2 - 43*x + 47,
    x^4 + x^3 + 8*x^2 + 42*x + 117
    ];
C2_polys := [
    x^4 + 10*x^2 + 20,
    x^4 + x^3 + 16*x^2 + 16*x + 61,
    x^4 - 2*x^3 + 34*x^2 - 33*x + 61,
    x^4 - 2*x^3 + 44*x^2 - 43*x + 101,
    x^4 + x^3 + 21*x^2 + 21*x + 101,
    x^4 + 20*x^2 + 50,
    x^4 + x^3 + 15*x^2 - 17*x + 29,
    x^4 + 26*x^2 + 52
    ];
C2xC2_polys := [
    x^4 + 15*x^2 + 45,
    x^4 + x^3 + 26*x^2 + 26*x + 151,
    x^4 + 30*x^2 + 180,
    x^4 + 35*x^2 + 245,
    x^4 - x^3 + 36*x^2 - 36*x + 281,
    x^4 - x^3 + 33*x^2 - 107*x + 139,
    x^4 + x^3 + 54*x^2 - 56*x + 263,
    x^4 + x^3 + 62*x^2 - 1*x + 1021,
    x^4 - x^3 + 46*x^2 - 105*x + 951
    ];
prec := 2048;
reduced_prec := 1024;
i := 4;
chi := C2xC2_polys[i];
K := NumberField(chi);
OK := MaximalOrder(K);
GK, iK := ClassGroup(OK);
II := [ iK(g) : g in GK ];
RR := RealField(reduced_prec);
j := 1;
time JJ := [ RR | Real(ji) :
    ji in AbsoluteIgusaInvariants(II[j],prec)[[1,2,4]] ];;
time rels := [ AlgebraicRelation(ji,2) : ji in JJ ];
print "prms =", Factorization(&*[ LeadingCoefficient(h) : h in rels ]);

P<j1,j2,j4> := PolynomialRing(ZZ,3 : Global);
C2xC2_igusa := [
    // #1
    [
    [
    144*j1^2 - 7579908276975000*j1 + 1124406965607900390625,
    82944*j2^2 - 85120995781800000*j2 + 477442032169931640625,
    6879707136*j4^2 - 3263040106456320000*j4 - 440499626137492109375 ],
    [
    113423440865551165584*j1^2 - 375589417038251166785255175000*j1 - 15810771842525577518415849599609375,
    65331901938557471376384*j2^2 - 8506298717143516704007751400000*j2 + 51298902356585214506027305556640625,
    5418889274391710905842794496*j4^2 - 1758809387170264326514473528576000*j4 + 2074761742709448291960750532621890625
    ]
    ],
    // #2
    [
    [
    390958996697672252831289*j1^2
    - 34946408774522182013672542765056000000000*j1
    - 137170253004514305185171898368000000000000000,
    3518630970279050275481601*j2^2
    + 3422886878030638587067959247872000000000*j2
    - 21105607392604100724877426688000000000000000,
    285009108592603072314009681*j4^2
    + 29897866798881818510343616221268800000*j4
    - 116576568564313462862685187347968000000000
    ],
    [
    64979188346666658376812007276737418873063554093531825581760092795216169*x^2
    - 31604679959143378127157986419541021931482856278112805639871479954695782400000*x
    - 1187387926747920685042970985127419611193559800713001370223100444268298240000000000,
    584812695119999925391308065490636769857571986841786430235840835156945521*x^2
    - 12542105834501577457745467428614020423855564190789444050637611587583180800000*x
    + 16222635746988293470032679026954955923622243125956624201435998805032960000000000,
    47369828304719993956695953304741578358463330934184700849103107647712587201*x^2
    - 5431269542177272493105875968804694277708560556336835374574555302888299008000*x
    - 4375592856403251093519384437897752420755066650270538170019366549515915264000000
    ]
    ]
    // #3
    [
    [
    1458058630749315398913075617669382144*x^2 
    - 5497833233529980918376221969655634076015897990942400000*x
    + 143083230660356921029073220786072824556154311292567812211416015625,
    839841771311605669773931555777564114944*x^2
    - 19220481584787261984601683243019569101059175156851200000*x
    + 17731659629569464026776020906042949216279429885479692594541015625,
    69659835879669820673728978962414277949915136*x^2
    - 62060545789330291270604067731283063680001790732812288000*x
    + 108892164886428175738906780434860641099975742039283367062015625
    ]
    ],
    // #4
    [
    [
    4035383780929275190223327175581111427431609043009834974524646416*x^2 -
        397319419367710131861165039832286432917984808745594215509779854481085841339248575000*x
    - 815410451580009244629664101322686059416971120017040263578799232537271922689104990234375,
    258264561979473612174292939237191131355622978752629438369577370624*x^2
    - 106898100340360163450472423814018103012730756768823186668184745552549851043015400000*x
    - 4075742521069997612327873568380088292921617929939091871680325114090411366246787109375,
    264462911466980978866475969778883718508157930242692544890447227518976*x^2
    - 2009045540555414907478991986598395487632085659180394401955783386860423016340736000*x
    + 40642257646677244933615319003197135520803169459247630878687654949622826231466890625
    ]
    ],
    // #5
    [
    ],
    // #6
    [
    ],
    // #7
    [
    ],
    // #8
    [
    ],
    // #9
    [
    ]
    ];


function TransformationMatrix(I,s)
    assert I eq s(I);
    B := Basis(I);
    K := Domain(s);
    A := Matrix([ Eltseq(K!x) : x in B ]);
    As := Matrix([ Eltseq(s(x)) : x in B ]);
    return As*A^-1;
end function;

*/
