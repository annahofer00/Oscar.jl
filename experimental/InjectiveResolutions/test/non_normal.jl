# one-dimensional affine semigroup ring
kQ_ = monoid_algebra([[2],[3]],QQ)
N = quotient_ring_as_module(ideal(kQ_,[]))
inj_res = injective_resolution(N,3)

# k[Q]-module with 2 generators
_KQ = direct_sum(quotient_ring_as_module(ideal(kQ_,[])), quotient_ring_as_module(ideal(kQ_,[])))[1]
_x1,_x2 = gens(kQ_)
_N = sub(_KQ,[_x1*_KQ[1],_x2*_KQ[2]])[1]

inj_res = injective_resolution(_N,3)

# first example of affine semigroup ring (2-dimensional)
kQ = monoid_algebra([[2,0],[3,0],[0,2],[0,3]],QQ)
KQ = quotient_ring_as_module(ideal(kQ,[]))
inj_res = injective_resolution(KQ,3)

# injective resolution over non-normal monoid algebra
# shift k[Q] by hand 
_M = quotient_ring_as_module(ideal(kQ,[]))
M = twist(_M,-grading_group(kQ)([2,2]))
inj_res = injective_resolution(M,5)

inj_res_not_shifted = injective_resolution(_M,3)

irr_res = irreducible_resolution(M,3)

# Example 4.5 in Katthän
kQ = monoid_algebra([[0,0,1],[1,0,1],[0,2,1],[0,3,1],[1,3,1],[1,2,1]],QQ)
KQ = quotient_ring_as_module(ideal(kQ,[]))
i = 3
a = compute_shift(KQ,3)
_KQ = twist(KQ,-grading_group(kQ)([2,6,4]))

M = _KQ
irr_res = irreducible_resolution(M,3)
inj_res = injective_resolution(KQ,3)

# non CM example
# Q does not generate ZZ^d! 
kQ = monoid_algebra([[4,0],[3,1],[1,3],[0,4]],QQ)
KQ = quotient_ring_as_module(ideal(kQ,[]))
a = compute_shift(KQ,3)
_KQ = twist(KQ,-grading_group(kQ)([8,8]))
M = _KQ
irr_res = irreducible_resolution(M,3)

#non-normal
kQ = monoid_algebra([[2,0],[0,1],[1,1]],QQ)
KQ = quotient_ring_as_module(ideal(kQ,[]))
inj_res = injective_resolution(KQ,3)

_KQ = twist(KQ,-grading_group(kQ)([1,2]))
irr_res = irreducible_resolution(_KQ,3)

x1,x2,x3 = gens(kQ)
_Wi = direct_sum(quotient_ring_as_module(ideal(kQ,[x2^3,x2*x3,x3^3])),quotient_ring_as_module(ideal(kQ,[x3,x1])))[1]

#build an irreducible resolution by hand
x1,x2,x3,x4 = gens(kQ)
W0 = _M #this is just kQ 
h0 = hom(M,_M,[x1*x3*_M[1]])
h0 = hom(M,W0,[W0[1]])
is_injective(h0)
is_welldefined(h0)
CK,h = quo(W0,image(h0)[1])
CK0 = cokernel(h0)
CK0_ = twist(CK0,grading_group(kQ)([2,2]))

W1,_ = direct_sum(
    # quotient_ring_as_module(ideal(kQ,[x3^2,x3*x4])), 
    #                quotient_ring_as_module(ideal(kQ,[x1^2,x1*x2])),
                   quotient_ring_as_module(ideal(kQ,[x3])),
                   quotient_ring_as_module(ideal(kQ,[x1]))
                   )
_h1 = hom(CK0_,W1,[W1[1] + W1[2]])
is_injective(_h1)
is_welldefined(_h1)

h1 = hom(W0,W1,[W1[1] + W1[2] + W1[3] + W1[4]])

CK1 = cokernel(h1)

W2,_ = direct_sum(quotient_ring_as_module(ideal(kQ,[x3^2,x3*x4,x1^2,x1*x2])),
                 quotient_ring_as_module(ideal(kQ,[x1,x2,x3,x4])))

_h2 = hom(CK1,W2,[W2[1];W2[1];W2[2];W2[2]])
is_injective(_h2) #this is not injective :(
K = kernel(_h2)[1]

h2 = hom(W1,W2,[W2[1];W2[1];W2[2];W2[2]])

# ring homomorphism
phi = Oscar.hom(kQ,kQsat,[x^2,x^3,y^2,y^3])

M = quotient_ring_as_module(ideal(kQ,[]))
N = quotient_ring_as_module(ideal(kQsat,[]))

p_F = ideal(kQ.algebra,gens(kQ.algebra))
F = FaceQ(p_F,kQ.cone)
J = IndecInj(F,[3,1])

kQsat = saturation(kQ)
x,y = gens(kQsat)

I = ideal(kQsat,[x^2,x^3,y^2,y^3])
inj_res = injective_resolution(I,3)

m = ideal(kQsat,[x,y])
H1 = local_cohomology(I,m,1)
is_zero(H1)

H2 = local_cohomology(I,m,2)
is_zero(H2)

H3 = local_cohomology(I,m,3)
is_zero(H3)

a,b,c,d = gens(kQ)
I1 = ideal(kQsat,[x])
I2 = ideal(kQsat,[y])

H1 = local_cohomology(I1,m,1)
is_zero(H1)
s = H1.sectors[5].sector

H2_ = local_cohomology(I2,m,1)
is_zero(H2_)
s = H2_.sectors[4].sector