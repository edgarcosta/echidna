function Dx(f)
   // Returns the derivative of f with respect to the 
   // generator of the base field, or with respect to the 
   // field generator, if an infinite extension.

   K := Parent(f); y := K.1;
   if Degree(K) eq Infinity() then 
      F := ConstantField(K);
      return K!Derivative(FunctionField(F)!f);
   end if;
   F := BaseField(K); x := K!F.1; 
   P := FunctionField(ConstantField(K));
   a := Eltseq(f);
   Y := [ y^i : i in [0..#a-1] ]; 
   Dy := Evaluate(Derivative(DefiningPolynomial(K)),y);
   return &+[ Derivative(P!a[i])*Y[i] : i in [1..#a] ] +
          &+[ (i-1)*a[i]*Y[i-1] : i in [2..#a] ]*Dy;
end function;

intrinsic Derivative(f::FldFunElt,x::FldFunElt) -> FldFunElt
   {Returns the derivative of f with respect to x.}

   K := Parent(f); y := K.1;
   require Parent(x) eq K : "Arguments must have the same parent.";
   print "D(f) =", Dx(f);
   print "D(x) =", Dx(x);
   if x eq BaseField(K).1 then return Dx(f); end if;
   require not IsConstant(x) : "Arguments must have the same parent.";
   return Dx(f)/Dx(x); 
end intrinsic;

