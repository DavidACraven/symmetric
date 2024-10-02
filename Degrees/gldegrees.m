intrinsic LusztigaFunction(pa::[RngIntElt]) -> RngIntElt
{Returns the Lusztig a-function associated to the partition pa, i.e., the sum over i of (i-1) times the size of the ith part of pa.}
require IsPartition(pa): "Input must be a partition";
return &+[(i-1)*pa[i]:i in [1..#pa]];
end intrinsic;

intrinsic LusztigAFunction(pa::[RngIntElt]) -> RngIntElt
{Returns the Lusztig A-function associated to the partition pa, i.e., the degree of the generic degree of the unipotent character, so the sum of the Lusztig a-function and n+1 choose 2 minus the sum of the hook lengths of pa.}
require IsPartition(pa): "Input must be a partition";
require pa[#pa] ge 1: "Input cannot have trailing zeros";
n:=&+pa;
return &+[(i-1)*pa[i]:i in [1..#pa]]+(n*(n+1) div 2)-&+[HookLength(pa,i,j):j in [1..pa[i]],i in [1..#pa]];
end intrinsic;


intrinsic GLGenericDegree(pa::[RngIntElt]) -> RngUPolElt
{ Computes the generic degree of the unipotent character of GLn(q) associated to the partition pa. }
require IsPartition(pa): "Input must be a partition";
require pa[#pa] ge 1: "Input cannot have trailing zeros";
n:=&+pa;
R<q>:=PolynomialRing(Integers());
return q^(&+[(i-1)*pa[i]:i in [1..#pa]])*&*[q^i-1:i in [1..n]] div &*[q^HookLength(pa,i,j)-1:j in [1..pa[i]],i in [1..#pa]];
end intrinsic;

intrinsic GUGenericDegree(pa::[RngIntElt]) -> RngUPolElt
{ Computes the generic degree of the unipotent character of GUn(q) associated to the partition pa. }
require IsPartition(pa): "Input must be a partition";
require pa[#pa] ge 1: "Input cannot have trailing zeros";
n:=&+pa;
R<q>:=PolynomialRing(Integers());
poly:=q^(&+[(i-1)*pa[i]:i in [1..#pa]])*&*[(-q)^i-1:i in [1..n]] div &*[(-q)^HookLength(pa,i,j)-1:j in [1..pa[i]],i in [1..#pa]];
return poly/LeadingCoefficient(poly);
end intrinsic;