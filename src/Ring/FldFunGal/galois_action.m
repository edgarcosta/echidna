
intrinsic GaloisPermutionGroup(p::PlcFun) -> GrpPerm
    {}
    K := ResidueClassField(p);
    G, _, m := GaloisGroup(K);
    return G, m;
end intrinsic;
