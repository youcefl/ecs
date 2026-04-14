/*
* Created on 2025.11.06
* Copyright (c) 2025-2026 Youcef Lemsafer.
* License: MIT
*/


/******************************************************************************
* Creates and returns a logger
* rank: positive integer: rank of the instance of the searcher being executed,
* -1 means there is only one instance.
* Returns a vector [logFile, logFunc] where logFile is the log file descriptor
* and logFunc is the closer to use for writting messages to the log.
******************************************************************************/
ec_create_logger(rank) = 
{
    my(logFileName = "");
    my(logFile);
    my(logFunc);
    if(rank == -1,
        logFileName = "ecsearch.log"
    ,
        logFileName = strprintf("ecsearch_%04d.log", rank)
    );
    my(logFile = fileopen(logFileName, "a"));
    my(logFunc = (s[..]) ->
        for(i=1, #s, filewrite1(logFile, s[i]));
        filewrite(logFile, "");
    );
    return([logFile, logFunc, logFileName])
}


/******************************************************************************
* Closes the log
* logger: value returned by ec_create_logger
******************************************************************************/
ec_close_log(logger) = 
{
    fileclose(logger[1])
}


/******************************************************************************
* Flush the log
* logger: value returned by ec_create_logger
******************************************************************************/
ec_flush_log(logger) =
{
    fileflush(logger[1])
}


/******************************************************************************
******************************************************************************/
ec_parallel_search(T, p, a0, a1) =
{
    my(delta = abs(a1 - a0));
    parapply(x -> ec_search(p, x[1], x[2], x[3]),
        vector(T, i,
            [ a0 + floor((i - 1) * delta / T),
              a0 + floor(i * delta / T) - 1,
              i
            ]
        )
    )
}


/******************************************************************************
* p must be prime
* a0 must be > 2 to produce meaningful curve
******************************************************************************/
ec_search(p, a0, a1, {rank}) =
{
    my(logger = if(rank, ec_create_logger(rank), ec_create_logger(-1)));
    my(msg = "S");
    if(rank, msg = Str("{", rank, "} s"));
    print(msg, "earching range ["a0, ", ", a1, "], log file: `", logger[3], "'");
    my(logFile = logger[1]);
    my(lprint = logger[2]);
    my(curve_cnt = 0);
    lprint("a0=", a0, ", a1=", a1);
    ec_flush_log(logger);

    my(start_time = getwalltime());
    for(A=a0, a1,
        /* We silently get rid of cases where A^2-4 is a quadratic
        * residue mod p because such cases won't yield a safe curve.
        * Of course this test can be deactivated if one wants to see
        * how many curves would have been selected absent this criterion.
        * This test incurs a massive speed-up because it is negative for lots
        * of values of A which causes us to skip all subsequent costly
        * computations.
        */
        if(kronecker(A^2 - 4, p) == -1,
            curve_cnt = curve_cnt + 1;
            my(N);
            my(E = ellinit([0, A, 0, 1, 0], p));
            if(!ellissupersingular(E),
                if(N = ellsea(E, 2),
                    my(F = factor(N, 3));
                    my(N_twist = 2*p + 2 - N);
                    if(isprime(N / (F[1,1] ^ F[1,2])),
                        my(report = Str("y^2 = x^3",
                            if(A < 0, Str("-", -A), Str("+", A)),
                            "*x^2+x is not super-singular and has order = ",
                            F[1,1], "^", F[1,2], "*q (q prime)"));
                        my(G = factor(N_twist, 3));
                        my(N_twist_divisor = G[1,1] ^ G[1,2]);
                        my(N_twist_cofac = N_twist / N_twist_divisor);
                        my(isWin = 0);
                        if(isprime(N_twist_cofac),
                            report = Str(report, " ** EPIC WIN!!! N_twist/",
                               N_twist_divisor, " is a prime! **");
                            isWin = 1
                        ,
                            report = Str(report, " ** FAIL: N_twist/", N_twist_divisor, " is not a prime **")
                        );
                        lprint(report);
                        ec_flush_log(logger);
                        if(isWin,
                            /* Winner? Put it on trial... */
                            ec_trial(p, A, lprint)
                        )
                    )
                )
            );
            if(curve_cnt % 1000 == 0,
                lprint("Processed ", curve_cnt, " curves")
            )
        )
    );
    lprint("Done. Processed range [", a0, ", ", a1, "], ",
            curve_cnt, " curves tested in ", strtime(getwalltime() - start_time),
            ".");
    ec_close_log(logger);
}


/******************************************************************************
* Trial factors N searching for factors up to bound.
* Prints results e.g. N = <value> = 2^3 * <N/8> \n isprime(N/8) = 1
******************************************************************************/
ec_trial_factor(N, N_name, lprint) =
{
    my(allFactorsButLastAsStr = "");
    my(factorsOfN = factor(N, 3));
    my(factorsOfNAsStr = "");
    my(separator = "");
    my(factorsLength = matsize(factorsOfN)[1]);
    for(i = 1, factorsLength,
        my(exponentAsStr);
        my(exponent = factorsOfN[i, 2]);
        if(exponent == 1, exponentAsStr = "", exponentAsStr = Str("^", Str(exponent)));
        factorsOfNAsStr = Str(factorsOfNAsStr, separator, Str(factorsOfN[i, 1]), exponentAsStr);
        if(i != factorsLength,
            allFactorsButLastAsStr = factorsOfNAsStr;
        );
        separator = " * "
    );
    lprint("    = ", factorsOfNAsStr);
    my(lastCofactor = factorsOfN[factorsLength, 1]^factorsOfN[factorsLength, 2]);
    my(lastCofactorAsStr = Str(N_name, "/(", allFactorsButLastAsStr, ")"));
    my(islastCofactorPrime = isprime(lastCofactor));
    my(isPrimeStr = "");
    if(islastCofactorPrime, isPrimeStr = "is a prime",
                            isPrimeStr = "is not a prime"
    );
    lprint("  ", lastCofactorAsStr, " ", isPrimeStr);
    return([factorsOfN[1,1] ^ factorsOfN[1,2], lastCofactor, islastCofactorPrime]);
}


/******************************************************************************
* Checks that given point H is on curve E.
* Reports error and returns 0 if it is not the case
* otherwise returns 1.
******************************************************************************/
ec_check_point_on_curve(E, H, lprint) =
{
    if(!ellisoncurve(E, H),
        lprint("Point ", H, " not on curve, this is unexpected! Aborting...");
        return(0);
    );
    return(1);
}


/******************************************************************************
* Checks whether the curve and its twist have acceptable cardinals.
* If true returns [1, N_fact, N_cofact] where N_fact is an array containing
* small factors of N and N_cofact the associated cofactor(s).
* If false returns [0, N_fact, N_cofact].
******************************************************************************/
ec_are_cardinal_and_twist_acceptable(P, N, N_twist, footer, lprint) =
{
    lprint("* Checking cardinal and twist cardinal");
    lprint("  N = #E(F_p) = ", N);
    my(N_fact = ec_trial_factor(N, "N", lprint));
    lprint("  N_twist = ", N_twist);
    my(N_twist_fact = ec_trial_factor(N_twist, "N_twist", lprint));
    my(N_cofact = N_fact[2]);
    my(is_N_cofact_prime = isprime(N_fact[2]));
    my(N_twist_cofact = N_twist_fact[2]);
    my(is_N_twist_cofact_prime = isprime(N_twist_fact[2]));
    if(!is_N_cofact_prime,
        lprint("N/2^k is not prime, aborting...");
        lprint(footer);
        return([0, N_fact, N_cofact]);
    );
    if(!is_N_twist_cofact_prime,
        my(tf_bound = 2^32);
        lprint("N_twist/2^k is not prime, trial factoring it to ", tf_bound);
        my(small_factor = ec_has_small_factor(N_twist_cofact, 2^8));
        if(small_factor,
            lprint("-> small factor found: ", small_factor, ", FAIL...");
            lprint(footer);
            return([0, N_fact, N_cofact])
        );
        my(N_twist_factors = factor(N_twist_cofact, tf_bound));
        my(distinct_factors_count = matsize(N_twist_factors)[1]);
        if(distinct_factors_count > 1,
            lprint("N_twist/2^k has factor: ",  N_twist_factors[1,1],
                    ", FAIL...");
            lprint(footer);
            return([0, N_fact, N_cofact])
        );
        lprint("N_twist/2^k has no factor below ", tf_bound);
        lprint("Need to fully factor N_twist/2^k to be able to take a decision...");
        N_twist_factors = factor(N_twist_cofact);
        distinct_factors_count = matsize(N_twist_factors)[1];
        lprint("-> Found ", distinct_factors_count, " factor(s)");
        if(distinct_factors_count > 2,
            lprint("N_twist/2^k has ", distinct_factors_count,
                " factors, aborting...");
            return([0, N_fact, N_cofact])
        );
        /* Case where N_twist/2^k is semi-prime = u*v
        * compute relative difference in length between u and v */
        my(u = N_twist_factors[1, 1]);
        my(v = N_twist_factors[2, 1]);
        delta_length_percent = (abs(log(u) - log(v)) * 100) / log(N_twist_cofact);
        if(delta_length_percent > 10.0,
            lprint("N_twist/2^k is semi-prime but difference in length of the two factors is > 10%, FAIL...");
            lprint(footer);
            return([0, N_fact, N_cofact])
        )
    );
    return([1, N_fact, N_cofact])
}


/******************************************************************************
* Compute the complex-multiplication field discriminant D as defined in
* https://safecurves.cr.yp.to/disc.html
* and check whether D > 2^100
******************************************************************************/
ec_check_cm_field_discriminant(P, N, lprint) =
{
    my(t = P + 1 - N);
    my(Dp = abs(t^2 - 4*P));
    lprint("* Trial factoring Dp = |t^2 - 4p| = ", Dp, " to 2^35...");
    my(tf_bound = 2^35);
    my(Dp_fact = factor(Dp, tf_bound));
    /* Compute non-square-free part */
    my(sq_part = 1);
    my(sq_part_text = "");
    my(sq_part_text_sep = "");
    for(i = 1, matsize(Dp_fact)[1],
        my(exponent = bitxor(Dp_fact[i, 2], bittest(Dp_fact[i, 2], 0)));
        if(exponent,
            sq_part = sq_part * Dp_fact[i, 1] ^ exponent;
            sq_part_text = Str(sq_part_text, sq_part_text_sep,
                               Dp_fact[i, 1], "^", exponent);
            sq_part_text_sep = "*";
        )
    );
    my(probabilityOfFailure = 1.0 / (tf_bound * log(tf_bound)));
    lprint("  square part of Dp: ", sq_part_text, 
          " (probability of a remaining non-squarefree factor is ~ ", probabilityOfFailure,
          ")");
    Dp = Dp / sq_part;
    my(D);
    if(Dp % 4 == 1, D = Dp
                  , D = 4 * Dp);
    my(discriminantLowerBound = 2^100);
    lprint("  Discriminant D = ", D);
    if(D > discriminantLowerBound,
        lprint("  Discriminant is OK with probability ~ ",
              (1 - probabilityOfFailure)*100, "%");
        return(1)
    );
    lprint("  Discriminant is below 2^100.");
    return(0) 
}


/******************************************************************************
* Finds a generator point on the curve
* E: the elliptic curve over F_p
* P: prime number, the p in E(F_p)
* A: coefficient of X^2 in the curve's equation
* h: largest power of 2 dividing N = #E(F_p)
* r: N/h, prime cofactor of h
******************************************************************************/
ec_find_generator(E, P, A, h, r, lprint) =
{
    lprint("* Searching for a generator point\n  A = ", A, "\n  h = ",
                h, "\n  r = ", r);
    my(x = 1);
    my(F(x) = x^3+A*x^2+x);
    my(foundGenerator = 0);
    while(!foundGenerator,
        my(y2 = F(x));
        if(kronecker(y2, P) == 1,
            lprint("  Attempting X = ", x);
            my(y = lift(sqrt(Mod(y2, P))));
            if(y > P - y, y = P - y);
            my(H = [x, y]);
            if(!ec_check_point_on_curve(E, H, lprint), return);
            my(G = ellmul(E, H, h)); /* Remove small factor */
            if(G == [0],
                H = [x, P - y];
                if(!ec_check_point_on_curve(E, H, lprint), return);
                G = ellmul(E, H, h); /* Remove small factor */
            );
            if(G != [0],
                my(rG = ellmul(E, G, r));
                my(rm1G = ellmul(E, G, r - 1));
                if((rG != [0]) || (rm1G == [0]),
                    lprint("[", lift(G[1]), ", ", lift(G[2]),
                        "] was about to be declared a generator but",
                        " something went wrong:\n[r]G=", rG,
                        "[r-1]G = ", rm1G)
                ,   lprint("Generator found: [", lift(G[1]),
                            ",\n", lift(G[2]), "]");
                    foundGenerator = 1;
                );
            );
        );
        x = x + 1
    )
}


/******************************************************************************
* Returns true if and only if n has a factor below given bound
******************************************************************************/
ec_has_small_factor(n, bound) =
{
    forprime(p=2, bound,
        if(gcd(p, n) != 1, return(p))
    );
    return(0)
}


/******************************************************************************
* Puts a curve of the Montgomery form on trial
******************************************************************************/
ec_trial(P, A, {printl}) =
{
    my(lprint = if(printl, printl, (s[..]) -> for(i=1, #s, print1(s[i])); print("")));
    my(header = Str("========================================",
                    "========================================"));
    my(footer = header);
    lprint(header);
    lprint("Trial for Y^2 = X^3 + ", A, "*X^2 + X (mod ", P, ")");
    lprint("--------------------------------------------------------------------------------");
    if(!isprime(P),
        lprint("P must be prime, FAIL...");
        lprint(footer);
        return;
    );
    my(E = ellinit([0, A, 0, 1, 0], P));
    lprint("* Is supersingular: ", ellissupersingular(E));
    my(N = ellcard(E));
    my(N_twist = 2*P + 2 - N);
    my(n_n_twist_probe_results = ec_are_cardinal_and_twist_acceptable(
                P, N, N_twist, footer, lprint)
    );
    if(!n_n_twist_probe_results[1],
        /* Gets rid of N or N_twist = 2^k*<small factor>*... */
        return
    );
    my(N_fact = n_n_twist_probe_results[2]);
    my(N_cofact = n_n_twist_probe_results[3]);

    /* Checks the complex-multiplication field discriminant */
    if(!ec_check_cm_field_discriminant(P, N, lprint),
        lprint("The CM field discriminant test did not pass, FAIL...");
        return
    );
    lprint("The curve passed the CM field discriminant test, continuing...");

    /* Find generator */
    ec_find_generator(E, P, A, N_fact[1], N_cofact, lprint);

    lprint(footer)
}


export(ec_create_logger);
export(ec_flush_log);
export(ec_close_log);
export(ec_search);
export(ec_check_point_on_curve);
export(ec_are_cardinal_and_twist_acceptable);
export(ec_has_small_factor);
export(ec_trial_factor);
export(ec_check_cm_field_discriminant);
export(ec_find_generator);
export(ec_trial);

