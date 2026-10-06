/* guided.c -- follow a known solution S through the search of the hvds/seq A101877 C solver (v9.7).
 *
 * This file is appended to the hvds sources (C_int.c with main renamed, pp.c, walker.c, mygmp.c,
 * mbh.c, prime.c, inverse.c) to form one translation unit; see run.sh.  It builds the solver's own
 * data structures for (n, k) with setup_pp() and pp_study(), then walks the solver's processing
 * order (pplist).  At every level it computes the discard that S implies, the limit and residue
 * (invsum) exactly as pp_find() computes them, and runs the solver's own walker to see whether that
 * discard is enumerated.  It reports the first level at which S is excluded.
 *
 * Usage: ./C_guided n k witness_file      (witness: comma-separated integers, all <= k)
 * With GUIDED_CONTINUE set in the environment it does not stop at the first exclusion: it forces
 * S's choice and carries on.  (After a forced choice the solver's spare is no longer its own, so later
 * limit checks are only indicative; the static "audit:" lines are exact either way.)
 */
static char* gin;          /* gin[x] = 1 iff x in S */
static int gcontinue;      /* GUIDED_CONTINUE: list every excluding level */
static int gexcluded;      /* number of levels that exclude S */

static int kept_value(pp_pp* pp, int idx, int* kept);

/* kept part of S inside structure pp, in units of 1/pp->denominator; returns nonzero on inconsistency */
static int struct_kept_sum(pp_pp* pp, mpz_t out) {
	int i, k, bad = 0;
	mpz_t t;
	mpz_init(t);
	mpz_set_ui(out, 0);
	for (i = 0; i < pp->valsize; ++i) {
		if (kept_value(pp, i, &k))
			bad = 1;
		if (k) {
			mpz_set_x(t, ppv_mpx(pp_value_i(pp, i)), pp->valnumsize);
			mpz_add(out, out, t);
		}
	}
	mpz_clear(t);
	return bad;
}

/* Is value idx of structure pp kept by S?  A value 1/x is kept iff x is in S.  A composite value
 * (the unique kept sum of a structure F resolved by pp_resolve_simple) is kept iff S keeps exactly
 * that sum inside F, and discarded iff S keeps nothing inside F. */
static int kept_value(pp_pp* pp, int idx, int* kept) {
	pp_value* v = pp_value_i(pp, idx);
	pp_pp* F;
	mpz_t ks, comp;
	int bad;

	if (v->self) {
		*kept = gin[v->parent];
		return 0;
	}
	F = &pppp[v->parent];
	mpz_init(ks);
	mpz_init(comp);
	bad = struct_kept_sum(F, ks);
	mpz_set_x(comp, wr_discard(F->wh, F->wrh), F->valnumsize);
	mpz_sub(comp, F->total, comp);
	if (mpz_cmp(ks, comp) == 0) {
		*kept = 1;
	} else if (mpz_sgn(ks) == 0) {
		*kept = 0;
	} else {
		gmp_printf("INCONSISTENT: S keeps %Zd/%Zd inside resolved pp_%d, whose only allowed kept sums are 0 and %Zd/%Zd\n",
				ks, F->denominator, F->pp, comp, F->denominator);
		*kept = 0;
		bad = 1;
	}
	mpz_clear(ks);
	mpz_clear(comp);
	return bad;
}

/* S's discard at one structure, in units of 1/pp->denominator, and its residue mod p */
static int s_discard(pp_pp* pp, mpz_t d, int* ndisc) {
	int j, k, inv = 0;
	mpz_t z;
	mpz_init(z);
	mpz_set_ui(d, 0);
	*ndisc = 0;
	for (j = 0; j < pp->valsize; ++j) {
		kept_value(pp, j, &k);
		if (!k) {
			mpz_set_x(z, ppv_mpx(pp_value_i(pp, j)), pp->valnumsize);
			mpz_add(d, d, z);
			inv = (inv + pp_value_i(pp, j)->inv) % pp->p;
			++*ndisc;
		}
	}
	mpz_clear(z);
	return inv;
}

/* residue of the p^a digit of a rational, as pp_find() computes it for a dependent structure */
static int digit_residue(pp_pp* pp, mpq_t r) {
	mpz_t z, zr;
	int res = 0;
	mpz_init(z);
	mpz_init(zr);
	mpz_fdiv_qr_ui(z, zr, mpq_denref(r), pp->pp);
	if (mpz_sgn(zr) == 0) {
		mpz_mul_ui(z, mpq_numref(r), invfast(mod_ui(z, pp->p), pp->p));
		res = mod_ui(z, pp->p);
	}
	mpz_clear(z);
	mpz_clear(zr);
	return res;
}

int guided(int target) {
	int i, j, bad = 0;
	pp_pp *pp, *nextpp;
	mpz_t z, d;
	mpq_t q, limit, t;

	mpz_init(z);
	mpz_init(d);
	mpq_init(q);
	mpq_init(limit);
	mpq_init(t);

	pp_study(target);
	printf("pplist has %d structures after pp_resolve_simple\n", pplistsize);
	/* a structure dropped by pp_resolve_simple (no nonempty kept subset) must get nothing from S */
	for (j = 1; j <= k0; ++j) {
		int inlist = 0;
		pp = &pppp[j];
		if (!pp->p)
			continue;
		for (i = 0; i < pplistsize; ++i)
			if (pplist[i] == pp)
				inlist = 1;
		if (!inlist && !pp->wrh) {
			mpz_t ks;
			mpz_init(ks);
			bad |= struct_kept_sum(pp, ks);
			if (mpz_sgn(ks)) {
				gmp_printf("DROPPED pp_%d, but S keeps %Zd/%Zd there\n", pp->pp, ks, pp->denominator);
				bad = 1;
			}
			mpz_clear(ks);
		}
	}
	/* static audit: an independent structure must, by the solver's rule, have residue 0 on its own */
	for (i = 0; i < pplistsize; ++i) {
		int nd, sinv;
		pp = pplist[i];
		if (pp->depend)
			continue;
		sinv = s_discard(pp, d, &nd);
		if (sinv != pp->invtotal) {
			mpz_sub(z, pp->total, d);
			mpz_set(mpq_numref(t), z);
			mpz_set(mpq_denref(t), pp->denominator);
			mpq_canonicalize(t);
			gmp_printf("audit: independent pp_%d: S's kept part %Qd has residue %d mod %d; the solver's rule demands 0\n",
					pp->pp, t, (pp->invtotal - sinv + pp->p) % pp->p, pp->p);
			if (mpz_cmp(d, pp->min_discard) < 0) {
				mpz_sub(z, pp->min_discard, d);
				gmp_printf("audit:   and S discards %Zd/%Zd less there than the solver's min_discard\n", z, pp->denominator);
			}
		}
	}
	printf("processing order (D = dependent, I = independent):");
	for (i = 0; i < pplistsize; ++i) {
		pplist[i]->wh = 0;
		printf(" %d%s", pplist[i]->pp, pplist[i]->depend ? "D" : "I");
	}
	printf("\n");

	for (i = 0; i < pplistsize; ++i) {
		int nd, sinv, invsum, found = 0, nres = 0;
		wrhp wrh;

		pp = pplist[i];
		sinv = s_discard(pp, d, &nd);

		/* limit and invsum exactly as pp_find() computes them */
		mpq_set(limit, pp->spare);
		if (!pp->depend && mpz_sgn(pp->min_discard) != 0) {
			mpz_set(mpq_numref(q), pp->min_discard);
			mpz_set(mpq_denref(q), pp->denominator);
			mpq_canonicalize(q);
			mpq_add(limit, limit, q);
		}
		mpq_mul_z(limit, limit, pp->denominator);
		mpz_fdiv_q(mpq_numref(limit), mpq_numref(limit), mpq_denref(limit));
		invsum = pp->depend ? digit_residue(pp, pp->spare) : pp->invtotal;

		/* run the solver's own walker and look for S's discard */
		pp->wh = new_walker(pp, mpq_numref(limit), invsum);
		while ((wrh = walker_findnext(pp->wh))) {
			++nres;
			mpz_set_x(z, wr_discard(pp->wh, wrh), pp->valnumsize);
			if (mpz_cmp(z, d) == 0) {
				found = 1;
				pp->wrh = wr_clone(pp->wh, wrh);
				break;
			}
		}
		printf("level %2d pp_%d (%s): %d values, S discards %d; S residue %d, required %d%s\n",
				i, pp->pp, pp->depend ? "dependent" : "independent", pp->valsize, nd, sinv, invsum,
				found ? "" : "  <-- S's discard is NOT enumerated");
		if (!found) {
			mpq_t corr;
			mpq_init(corr);
			printf("==> S is excluded at level %d (pp_%d)\n", i, pp->pp);
			gmp_printf("   S's discard here: %Zd/%Zd, walker limit %Zd/%Zd, walker results seen: %d\n",
					d, pp->denominator, mpq_numref(limit), pp->denominator, nres);
			/* The solver's spare at this level counts every later structure j at its provisional
			 * min_discard.  Replace those by S's actual discards and recompute the requirement. */
			mpq_set(corr, pp->spare);
			for (j = i + 1; j < pplistsize; ++j) {
				pp_pp* pj = pplist[j];
				int ndj;
				s_discard(pj, z, &ndj);
				mpz_sub(mpq_numref(t), z, pj->min_discard);
				mpz_set(mpq_denref(t), pj->denominator);
				mpq_canonicalize(t);
				if (mpz_divisible_ui_p(mpq_denref(t), pp->pp))
					gmp_printf("   later level %d pp_%d (%s): S's discard - provisional min_discard = %Qd"
							" (denominator divisible by %d)\n",
							j, pj->pp, pj->depend ? "dependent" : "independent", t, pp->pp);
				mpq_sub(corr, corr, t);
			}
			if (!pp->depend) {
				mpz_set(mpq_numref(q), pp->min_discard);
				mpz_set(mpq_denref(q), pp->denominator);
				mpq_canonicalize(q);
				mpq_add(corr, corr, q);
			}
			gmp_printf("   discard this level must make, given S's later choices: %Qd -> residue %d (S has %d)\n",
					corr, digit_residue(pp, corr), sinv);
			mpq_clear(corr);
			++gexcluded;
			if (!gcontinue)
				return 0;
		}
		if (i + 1 >= pplistsize) {
			printf("reached the end of pplist\n");
			break;
		}
		nextpp = pplist[i + 1];
		if (found)
			mpz_set_x(mpq_numref(q), wr_discard(pp->wh, pp->wrh), pp->valnumsize);
		else
			mpz_set(mpq_numref(q), d);     /* GUIDED_CONTINUE: force S's choice */
		mpz_sub(mpq_numref(q), mpq_numref(q), pp->min_discard);
		mpz_set(mpq_denref(q), pp->denominator);
		mpq_canonicalize(q);
		mpq_sub(nextpp->spare, pp->spare, q);
		if (mpq_sgn(nextpp->spare) < 0) {
			gmp_printf("==> spare negative after level %d: %Qd\n", i, nextpp->spare);
			return 0;
		}
		if (mpz_cmp_ui(mpq_numref(nextpp->spare), 1) <= 0
				&& !(mpz_cmp_ui(mpq_numref(nextpp->spare), 1) == 0
					&& mpz_cmp_ui(mpq_denref(nextpp->spare), k0) > 0)) {
			gmp_printf("pp_solution() reports success before level %d (spare %Qd)%s\n",
					i + 1, nextpp->spare, gexcluded ? "" : ": S is not excluded");
			return !gexcluded;
		}
	}
	if (gexcluded)
		printf("%d level(s) exclude S\n", gexcluded);
	return !bad && !gexcluded;
}

int main(int argc, char** argv) {
	int n, k, x, cnt = 0, mx = 0, r;
	FILE* f;

	if (argc != 4) {
		fprintf(stderr, "usage: %s n k witness_file\n", argv[0]);
		return 2;
	}
	n = atoi(argv[1]);
	k = atoi(argv[2]);
	f = fopen(argv[3], "r");
	if (!f) {
		perror(argv[3]);
		return 2;
	}
	gin = calloc(k + 2, 1);
	while (fscanf(f, " %d ,", &x) == 1) {
		if (x < 1 || x > k) {
			printf("element %d is outside 1..%d\n", x, k);
			return 2;
		}
		gin[x] = 1;
		++cnt;
		if (x > mx)
			mx = x;
	}
	fclose(f);
	printf("S: %d elements, max %d; n=%d k=%d\n", cnt, mx, n, k);
	gcontinue = getenv("GUIDED_CONTINUE") != NULL;
	clock_tick = sysconf(_SC_CLK_TCK);
	setup_pp(k);
	r = guided(n);
	printf("guided result: %s\n", r ? "S survives the search" : "S is excluded by the search");
	return 0;
}
