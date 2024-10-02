intrinsic PrintReducedFormPartition(pa::SeqEnum[RngIntElt]) -> MonStgElt
{Prints a partition in reduced form, suitable to including in a LaTeX document. So, for example, the partition with one 3 and nine 1s is printed as (3,1^9).}
str:="(";
eltset:=SequenceToSet(pa);
while eltset ne {} do
  n:=Maximum(eltset);
  Exclude(~eltset,n);
  mult:=Multiplicity(pa,n);
  if(mult eq 1) then
    str cat:=IntegerToString(n) cat ",";
  elif mult le 9 then
    str cat:=IntegerToString(n) cat "^" cat IntegerToString(mult) cat ",";
  else
    str cat:=IntegerToString(n) cat "^{" cat IntegerToString(mult) cat "},";
  end if;
end while;
Prune(~str);
str cat:=")";
return str;
end intrinsic; 