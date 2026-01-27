
kQ = monoid_algebra([[2,0],[3,0],[0,2],[0,3]],QQ)

p_F = ideal(kQ.algebra,gens(kQ.algebra))
F0 = convex_hull([0,0])
F = FaceQ(p_F,F0)
J = IndecInj(F,[3,1])

# the algorithm works for this :))


# ring homomorphism
phi = Oscar.hom(kQ,kQsat,[x^2,x^3,y^2,y^3])

M = quotient_ring_as_module(ideal(kQ,[]))
N = quotient_ring_as_module(ideal(kQsat,[]))

p_F = ideal(kQ.algebra,gens(kQ.algebra))
F = FaceQ(p_F,kQ.cone)
J = IndecInj(F,[3,1])
