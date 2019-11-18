////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Weierstrass Function                     //
//                         Power Series Expansions                    // 
//                               David Kohel                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////



intrinsic WeierstrassTate(t::RngSerElt,q::RngSerElt,n::RngIntElt)
    -> RngSerElt
    {}
    PS := Parent(q);
    require Parent(t) cmpeq PS : 
        "Arguments 1 and 2 must have the same parent.";
    require t ne 1 : "Argument 1 must not be 1."; 
    require 1/12 in BaseRing(PS) : 
        "2 and 3 must be units in the coefficient ring of arguments 1 and 2.";
    s := t^-1;
    oe := O(PS.1^n);
    wp := 1/12 + t/(1-t+oe)^2 - 2*&+[ q^k/(1-q^k+oe)^2 : k in [1..n] ];
    wp +:= &+[ (t*q^k)/(1-t*q^k+oe)^2 : k in [1..n] ];
    wp +:= &+[ (s*q^k)/(1-s*q^k+oe)^2 : k in [1..n] ];
    return wp;
end intrinsic;

