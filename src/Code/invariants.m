//////////////////////////////////////////////////////////////////////// 
//                     Basic Code Invariants                          // 
//                          David Kohel                               //
////////////////////////////////////////////////////////////////////////

/*
// Now in kernel:

intrinsic BaseField(C::Code) -> Rng
    {}
    return Field(C);
end intrinsic;
*/

intrinsic Support(C::Code) -> SetEnum
    {}
    return &join[ Support(v) : v in Basis(C) ];
end intrinsic;

