# class_number — finite ideal classes from bounded integral representatives

Integer coordinate boxes and multiplication structure constants produce a nonzero small-norm element in each ideal. Multiplying an inverse ideal by that element gives a bounded integral class representative; there are finitely many nonzero integral ideals of bounded norm, so finitely many classes. Every bounded representative factors into nonzero primes of no larger norm, so the classes of the finitely many nonzero primes of bounded norm generate the class group.

The bound is the class-number bound n!·Sⁿ at an integral basis e₁, …, eₙ, where S is the largest of 1 and the sums, one for each j and k, over i of the absolute integer coordinates of eᵢeⱼ along eₖ. It is a device of this argument, not Minkowski's bound, so its definition and the coordinate estimates behind it are the chapter's own, unexported.

## Members

| Member | Statement |
|---|---|
| `IntegralIdealFromElement` | A nonzero element a of an integral ideal I gives the integral ideal J = (a)·I⁻¹ in the inverse class, with IJ = (a) and N(I)·N(J) = \|N(a)\| |
| `BoundedClassRepresentative` | Every ideal class has a nonzero integral representative whose norm is at most the class-number bound |
| `BoundedIdealsCoverClasses` | At an integral basis the ideal classes are finite, at most as many as the nonzero integral ideals of bounded norm |
| `ClassNumberFinite` | The class number of every number field is finite: its ideal classes form a finite set |
| `ExponentProductClassInSubgroup` | A subgroup of the ideal class group that holds the class of every factor of a finite exponent product of nonzero integral ideals holds the class of the product |
| `BoundedPrimeClassesGenerate` | The nonzero prime ideals of norm at most the class-number bound are finitely many, and their classes generate the ideal class group |
