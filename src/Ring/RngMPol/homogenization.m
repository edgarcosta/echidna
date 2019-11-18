////////////////////////////////////////////////////////////////////////
//             Homogenization of Multivariate Polynomials             //
////////////////////////////////////////////////////////////////////////

intrinsic Homogenization(f::RngMPolElt,z::RngMPolElt) -> RngMPolElt
    {}
    require Parent(f) eq Parent(z) :
       "Arguments must be elements of the same ring.";
    require IsHomogeneous(z) and TotalDegree(z) eq 1 :
       "Argument 2 must be homogeneous of degree 1.";
    deg := TotalDegree(f);
    return &+[ MonomialCoefficient(f,mon) * mon *
       z^(deg-TotalDegree(mon)) : mon in Monomials(f) ];
end intrinsic;

intrinsic Homogenization(
    f::RngMPolElt,z::RngMPolElt,deg::RngIntElt) -> RngMPolElt
    {}
    require Parent(f) eq Parent(z) :
       "Arguments must be elements of the same ring.";
    require IsHomogeneous(z) and TotalDegree(z) eq 1 :
       "Argument 2 must be homogeneous of degree 1.";
    return &+[ MonomialCoefficient(f,mon) * mon *
       z^(deg-TotalDegree(mon)) : mon in Monomials(f) ];
end intrinsic;

