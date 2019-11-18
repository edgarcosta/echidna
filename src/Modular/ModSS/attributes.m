////////////////////////////////////////////////////////////////////////
//                 Supersingular Module Attributes                    //
////////////////////////////////////////////////////////////////////////

declare verbose SupersingularModule, 2;

declare attributes ModSS:
    p,
    auxiliary_level,
    ss_points,
    basis,
    monodromy_weights,
    atkin_lehner_primes,
    atkin_lehner_operators,
    hecke_primes,
    hecke_operators,
    decomp,
    cuspidal_subspace,
    eisenstein_subspace,
    uses_brandt,
    brandt_module,
    modular_symbols,
    ambient_space,
    dimension,
    rspace,
    // The following is associated to the Atkin-Lehner submodule or quotient
    ss_polynomials,
    ss_polynomial_indices,
    discriminant_forms;

declare attributes ModSSElt:
    element,
    parent;

