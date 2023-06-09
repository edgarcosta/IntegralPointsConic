function MinimalSolutionSet(solutions, a, z, tau)
    // exclude solutions under tau multiplication
    // sort solutions
    solutions_height := [Abs(&*tup) : tup in solutions];
    ParallelSort(~solutions_height, ~solutions);

    // exclude solutions under tau multiplication
    O_solutions := [a*x + z*y where x,y := Explode(tup) : tup in solutions];
    pl := InfinitePlaces(Parent(z))[1];
    tau_oo := Evaluate(q, pl);
    excluded := [];
    for i->x in O_solutions do
        if i in excluded then continue; end if;
        for j->y in O_solutions[i+1..#O_solutions] do
            if j+i in excluded then continue; end if;
            q := x/y;
            q_oo := Evaluate(q, pl);
            sign := q1 gt 0 select 1 else -1;
            // q = tau^k?
            // sign*tau1^k = q1
            k := Round(Log(tau_oo, Abs(q_oo)));
            if q eq sign*tau^k  then
                Append(~excluded, i+j);
            end if;
        end for;
    end for;
    return {@ [Integers() | x,y] where x,y := Explode(tup) : i->tup in solutions | i notin excluded @};
end function;

intrinsic IntegralPointsConic(abc::SeqEnum, values::SeqEnum) -> Assoc
{ given [a,b,c], returns the solutions to a x^2 + b x y + c y^2 in values, with x, y \in \Z
up to the action of the fundamental unit of the order associated to the conic
}
    // standardize conic, GCD(a,b,c) = 1 and a > 0
    g := GCD(abc);
    sign := abc[1] lt 0 select -1 else 1;
    den := sign*g;
    if den ne 1 then
        newabc := [elt div den : elt in abc];
        newvalues := { d div den : d in values | d mod g ne 0 };
        newres := $$(newabc, newvalues);
        res := AssociativeArray();
        for d in values do
            if d mod g eq 0 then
                res[d] := newres[d div den];
            else
                res[d] := {@ @};
            end if;
        end for;
        return res;
    end if;


    if #values eq 0 then
        return AssociativeArray();
    end if;

    assert g eq 1;
    assert a gt 0;


    D := b^2 - 4*a*c;

    require D gt 0 and not IsSquare(D): "only support indefinite conics at the moment";

    I := Ideal(BinaryQuadraticForms(D)![a,b,c]);
    O := Order(I);
    OF := Integers(NumberField(O));

    tau := FundamentalUnit(O);
    if Norm(tau) eq -1 then
     tau *:= tau;
    end if;

    // (a*x + z*y)*(a*x + sigma(z)*y) = a f(x, y)
    z := -O!Roots(PolynomialRing(OF)![a*c, b, 1])[1][1]; //  we need to work over a maximal order for Factorisation

    // Norm(tau) eq 1 => one is smaller than one, the other one is larger than 1
    tau0, tau1 := Explode([Evaluate(tau, pl) : pl in InfinitePlaces(O)]);
    assert tau0 gt 0 and tau1 gt 0;
    bound :=  Max(tau0, tau1);

    dmax := Max(Abs(Max(values)), Abs(Min(values)));
    bound *:= Abs(Parent(bound)!dmax*a);
    bound := Sqrt(bound)*(1 + 10^(-Precision(bound)/10));

    // Now we need to solve |a x + phi_i y| < bound = B
    // this defines a parallelogram defined by the 4 vertices
    // B/a, 0
    // -B/a, 0
    // -(B/a) (phi0 + phi1)/ (phi0 - phi1), (2 B)/(phi0 - phi1)
    // (B/a) (phi0 + phi1)/ (phi0 - phi1), -(2 B)/(phi0 - phi1)
    phi0, phi1 := Explode(Sort([Evaluate(z, pl) : pl in InfinitePlaces(O)]));
    den := Abs(phi0 - phi1);
    xbound := bound/a * Max(1, Abs(phi0 + phi1)/den);
    xbox := [Ceiling(-xbound) .. Floor(xbound)];
    ybound := 2*bound/den;
    ybox := [Ceiling(-ybound) .. Floor(ybound)];

    // it seems cheaper to first check f(tup) in ds, and then restrict to the diamond
    values_set := SequenceToSet(values);
    //fn := func<tup | a*tup[1]^2 + b*tup[1]*tup[2] + c*tup[2]^2>;
    //solutions := [tup : tup in rectangle | fn(tup) in values_set and Abs(a*x + phi0*y) le bound and Abs(a*x + phi1*y) le bound where x,y := Explode(tup)];

    time solutions1 := &cat [
            [ elt : elt in [[x, y, Evaluate(fx, y)] : y in ybox | Abs(ax + phi0*y) le bound and Abs(ax + phi1*y) ] | elt[3] in values_set]
            where ax := a*x where fx := Polynomial(abc) : x in xbox
            ];

    // Abs(a*x + phi*y) <= B <=> a*x + phi*y < B and a*x + phi*y > -B <=> (because a > 0) x < (B - phi*y)/a and x > -(B + phi*y)/a
    xbox_giveny := func<y | [Ceiling(Max(-(bound + phi0*y)/a, -(bound + phi1*y)/a)) .. Floor(Min((bound-phi0*y)/a, (bound-phi1*y)/a))]>;
    time solutions := &cat [
        [ elt : elt in [[x, y, Evaluate(fy, x)] : x in xbox_giveny(y)] | elt[3] in values_set] where fy := Polynomial([c,b,a]) : x in xbox];
    assert solutions1 eq solutions;


    // group solutions by value
    res := AssociativeArray();
    for d in values do
      res[d] := [];
    end for;
    // group solutions by value
    for elt in solutions do
        Append(~res[elt[3]], elt[1..2]);
    end for;
    for d in Keys(res) do
        // sort solutions
        solutions_height := [Abs(&*tup) : tup in res[d]];
        ParallelSort(~solutions_height, ~res[d]);
        // extract minimal set
        res[d] := MinimalSolutionSet(res[d], a, z, tau);
    end for;

    return res;
end intrinsic;


function IntegralSolutionsNaive(f, d : abs:=false, Bound:=false)
    _<x,y> := Parent(f);
    g := GCD(Coefficients(f - d));
    f div:= g;
    d div:= g;

    if d mod GCD(Coefficients(f)) ne 0 then
        return [];
    end if;

    if LeadingCoefficient(f) lt 0 then
        f *:= -1;
        d *:= -1;
    end if;

    c, b, a := Explode(Coefficients(g)) where _, g := IsUnivariate(Evaluate(f, [x, 1]));
    D := b^2 - 4*a*c;

    I := Ideal(BinaryQuadraticForms(D)![a,b,c]);
    O := Order(I);
    OF := Integers(NumberField(O));

    z := -O!Roots(PolynomialRing(OF)![a*c, b, 1])[1][1]; //  we need to work over a maximal order for Factorisation
    tau := FundamentalUnit(O);
    if Norm(tau) eq -1 then
     tau *:= tau;
    end if;

    if Bound cmpeq false then
        Bound := 10*Abs(D*Ceiling(Max([Evaluate(tau, pl) : pl in InfinitePlaces(O)]))*d*a);
    end if;

    C := Conic(ProjectiveClosure(Curve(AffineSpace(Parent(f)), f - d)));
    solutions := [ Eltseq(elt)[1..2] : elt in RationalPoints(ChangeRing(C, Rationals()) : Bound:=Bound) | &and[x in Integers() : x in Eltseq(elt)] ];
    if abs then
        C := Conic(ProjectiveClosure(Curve(AffineSpace(Parent(f)), f + d)));
        solutions cat:= [ Eltseq(elt)[1..2] : elt in RationalPoints(ChangeRing(C, Rationals()) : Bound:=Bound) | &and[x in Integers() : x in Eltseq(elt)] ];
    end if;



    // sort solutions
    solutions_height := [<Max([Abs(Evaluate(a*x + z*y, pl)) : pl in InfinitePlaces(O)]), Abs(x*y)> where x,y := Explode(tup) : tup in solutions];
    ParallelSort(~solutions_height, ~solutions);

    return MinimalSolutionSet(solutions, a, z, tau);
end function;

