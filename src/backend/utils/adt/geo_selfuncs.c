/*-------------------------------------------------------------------------
 *
 * geo_selfuncs.c
 *	  Selectivity routines registered in the operator catalog in the
 *	  "oprrest" and "oprjoin" attributes.
 *
 * Portions Copyright (c) 1996-2021, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/utils/adt/geo_selfuncs.c
 *
 *	XXX These are totally bogus.  Perhaps someone will make them do
 *	something reasonable, someday.
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "utils/builtins.h"
#include "utils/geo_decls.h"

#include "access/htup_details.h"
#include "catalog/pg_statistic.h"
#include "nodes/pg_list.h"
#include "optimizer/pathnode.h"
#include "optimizer/optimizer.h"
#include "utils/lsyscache.h"
#include "utils/typcache.h"
#include "utils/selfuncs.h"
#include "utils/rangetypes.h"
#include "utils/rangetypes.h"

double _calc_hist_selectivity_scalar(TypeCacheEntry *typcache,
                                    const RangeBound *constbound,
                                    const RangeBound *hist, int hist_nvalues,
                                    bool equal);

/*
 * Look up the fraction of values less than (or equal, if 'equal' argument
 * is true) a given const in a histogram of range bounds.
 */
double calc_hist_selectivity_hist(TypeCacheEntry *typcache,
                                         const RangeBound *hist1, int nhist1,
                                         const RangeBound *hist2, int nhist2,
                                         bool equal)
{
    int         i;
    int         idx1;
    int         idx2;
    RangeBound  *chosed_bound;
    double      cur_selec;
    RangeBound  *old_bound;
    int         cur_bin_idx;
    double      cur_bin_area;
    double      cur_bin_height;
    double      trapezoid_base1;
    double      trapezoid_base2;
    double      trapezoid_height;
    double      *area_values;
    double      selec;

    idx1 = idx2 = 0;
    cur_bin_idx = -1;
    area_values = (double *) palloc(sizeof(double) * (nhist1 - 1));
    memset(area_values, 0, sizeof(double) * (nhist1 - 1));
    selec = 0;
    
    /* loop until finishing traversing all range bounds in hist1 */
    while (idx1 < nhist1)
    {
        if (idx2 >= nhist2)
        {
            // finished reading lower2
            if (cur_bin_idx < 0)
            {
                // area of every bin in upper1 is 0, finish
                break;
            }
            else
            {
                area_values[cur_bin_idx] = (cur_bin_height == 0) ? 0 : cur_bin_area / cur_bin_height;
                cur_bin_area = 0;
                cur_bin_height = 0;
                cur_bin_idx++;
                idx1++;
            }
        }
        else
        {
            if (range_cmp_bounds(typcache, &hist1[idx1], &hist2[idx2]) <= 0)
            {
                // upper is smaller
                chosed_bound = &hist1[idx1];
                cur_selec = 1 - _calc_hist_selectivity_scalar(typcache, chosed_bound, hist2, nhist2, equal);
                if (cur_bin_idx < 0)
                {
                    // first bin
                    cur_bin_idx = 0;
                }
                else
                {
                    // finish a bin and move to a new one
                    trapezoid_base2 = cur_selec;
                    trapezoid_height = (double) DatumGetFloat8(FunctionCall2Coll(&typcache->rng_subdiff_finfo,
                                                                                typcache->rng_collation,
                                                                                chosed_bound->val, 
                                                                                old_bound->val));
                    cur_bin_area += (trapezoid_base1 + trapezoid_base2) * trapezoid_height / 2;
                    cur_bin_height += trapezoid_height;
                    area_values[cur_bin_idx] = (cur_bin_height == 0) ? 0 : cur_bin_area / cur_bin_height;
                    cur_bin_idx++;
                }
                cur_bin_area = 0;
                cur_bin_height = 0;
                trapezoid_base1 = cur_selec;
                trapezoid_base2 = trapezoid_height = 0;
                old_bound = chosed_bound;
                idx1++;
            }
            else
            {
                // lower is smaller
                chosed_bound = &hist2[idx2];
                cur_selec = 1 - idx2 / (nhist2 - 1.0);
                if (cur_bin_idx < 0)
                {
                    idx2++;
                    continue;
                }
                trapezoid_base2 = cur_selec;
                trapezoid_height = (double) DatumGetFloat8(FunctionCall2Coll(&typcache->rng_subdiff_finfo,
                                                                            typcache->rng_collation,
                                                                            chosed_bound->val, 
                                                                            old_bound->val));
                cur_bin_area += (trapezoid_base1 + trapezoid_base2) * trapezoid_height / 2;
                cur_bin_height += trapezoid_height;
                trapezoid_base1 = cur_selec;
                trapezoid_base2 = trapezoid_height = 0;
                old_bound = chosed_bound;
                idx2++;
            }
        }
    }
    
    printf("area_values = [");
    for (i = 0; i < (nhist1 - 1); i++)
    {
        selec += area_values[i];
        printf("%lf", area_values[i]);
        if (i < nhist1 - 2)
            printf(", ");
    }
    printf("]\n");
    pfree(area_values);
    selec /= (nhist1 - 1);
    return selec;
}

/*
 *	Selectivity functions for geometric operators.  These are bogus -- unless
 *	we know the actual key distribution in the index, we can't make a good
 *	prediction of the selectivity of these operators.
 *
 *	Note: the values used here may look unreasonably small.  Perhaps they
 *	are.  For now, we want to make sure that the optimizer will make use
 *	of a geometric index if one is available, so the selectivity had better
 *	be fairly small.
 *
 *	In general, GiST needs to search multiple subtrees in order to guarantee
 *	that all occurrences of the same key have been found.  Because of this,
 *	the estimated cost for scanning the index ought to be higher than the
 *	output selectivity would indicate.  gistcostestimate(), over in selfuncs.c,
 *	ought to be adjusted accordingly --- but until we can generate somewhat
 *	realistic numbers here, it hardly matters...
 */

/*
 * Range Overlaps Join Selectivity.
 */
Datum
rangeoverlapsjoinsel(PG_FUNCTION_ARGS)
{
    PlannerInfo *root = (PlannerInfo *) PG_GETARG_POINTER(0);
    Oid         operator = PG_GETARG_OID(1);
    List       *args = (List *) PG_GETARG_POINTER(2);
    JoinType    jointype = (JoinType) PG_GETARG_INT16(3);
    SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) PG_GETARG_POINTER(4);
    Oid         collation = PG_GET_COLLATION();

    double      selec = 0.005;

    VariableStatData vardata1;
    VariableStatData vardata2;
    Oid         opfuncoid;
    AttStatsSlot sslot1;
    AttStatsSlot sslot2;
    int         nhist1;
    int         nhist2;
    RangeBound *hist_lower1;
    RangeBound *hist_upper1;
    RangeBound *hist_lower2;
    RangeBound *hist_upper2;
    int         i;
    Form_pg_statistic stats1 = NULL;
    Form_pg_statistic stats2 = NULL;
    TypeCacheEntry *typcache = NULL;
    bool        join_is_reversed;
    bool        empty;


    get_join_variables(root, args, sjinfo,
                       &vardata1, &vardata2, &join_is_reversed);

    typcache = range_get_typcache(fcinfo, vardata1.vartype);
    opfuncoid = get_opcode(operator);

    memset(&sslot1, 0, sizeof(sslot1));
    memset(&sslot2, 0, sizeof(sslot2));

    /* Can't use the histogram with insecure range support functions */
    if (!statistic_proc_security_check(&vardata1, opfuncoid))
        PG_RETURN_FLOAT8((float8) selec);
    if (!statistic_proc_security_check(&vardata2, opfuncoid))
        PG_RETURN_FLOAT8((float8) selec);

    if (HeapTupleIsValid(vardata1.statsTuple))
    {
        stats1 = (Form_pg_statistic) GETSTRUCT(vardata1.statsTuple);
        /* Try to get fraction of empty ranges */
        if (!get_attstatsslot(&sslot1, vardata1.statsTuple,
                             STATISTIC_KIND_BOUNDS_HISTOGRAM,
                             InvalidOid, ATTSTATSSLOT_VALUES))
        {
            ReleaseVariableStats(vardata1);
            ReleaseVariableStats(vardata2);
            PG_RETURN_FLOAT8((float8) selec);
        }
    }
    if (HeapTupleIsValid(vardata2.statsTuple))
    {
        stats2 = (Form_pg_statistic) GETSTRUCT(vardata2.statsTuple);
        /* Try to get fraction of empty ranges */
        if (!get_attstatsslot(&sslot2, vardata2.statsTuple,
                             STATISTIC_KIND_BOUNDS_HISTOGRAM,
                             InvalidOid, ATTSTATSSLOT_VALUES))
        {
            ReleaseVariableStats(vardata1);
            ReleaseVariableStats(vardata2);
            PG_RETURN_FLOAT8((float8) selec);
        }
    }

    nhist1 = sslot1.nvalues;
    hist_lower1 = (RangeBound *) palloc(sizeof(RangeBound) * nhist1);
    hist_upper1 = (RangeBound *) palloc(sizeof(RangeBound) * nhist1);
    for (i = 0; i < nhist1; i++)
    {
        range_deserialize(typcache, DatumGetRangeTypeP(sslot1.values[i]),
                          &hist_lower1[i], &hist_upper1[i], &empty);
        /* The histogram should not contain any empty ranges */
        if (empty)
            elog(ERROR, "bounds histogram contains an empty range");
    }

    nhist2 = sslot2.nvalues;
    hist_lower2 = (RangeBound *) palloc(sizeof(RangeBound) * nhist2);
    hist_upper2 = (RangeBound *) palloc(sizeof(RangeBound) * nhist2);
    for (i = 0; i < nhist2; i++)
    {
        range_deserialize(typcache, DatumGetRangeTypeP(sslot2.values[i]),
                          &hist_lower2[i], &hist_upper2[i], &empty);
        /* The histogram should not contain any empty ranges */
        if (empty)
            elog(ERROR, "bounds histogram contains an empty range");
    }

    // LOGIC start
    printf("===1===");
    printf("hist_lower = [");
    for (i = 0; i < nhist1; i++)
    {
        printf("%d", DatumGetInt16(hist_lower1[i].val));
        if (i < nhist1 - 1)
            printf(", ");
    }
    printf("]\n");
    printf("hist_upper = [");
    for (i = 0; i < nhist1; i++)
    {
        printf("%d", DatumGetInt16(hist_upper1[i].val));
        if (i < nhist1 - 1)
            printf(", ");
    }
    printf("]\n");


    printf("===2===");
    printf("hist_lower = [");
    for (i = 0; i < nhist2; i++)
    {
        printf("%d", DatumGetInt16(hist_lower2[i].val));
        if (i < nhist2 - 1)
            printf(", ");
    }
    printf("]\n");
    printf("hist_upper = [");
    for (i = 0; i < nhist2; i++)
    {
        printf("%d", DatumGetInt16(hist_upper2[i].val));
        if (i < nhist2 - 1)
            printf(", ");
    }
    printf("]\n");

    double left = calc_hist_selectivity_hist(typcache, hist_upper1, nhist1, hist_lower2, nhist2, false);
    double right = calc_hist_selectivity_hist(typcache, hist_upper2, nhist2, hist_lower1, nhist1, false);
    selec = 1 - (left + right);
    printf("left:%lf\tright:%lf\tselec:%lf\n", left, right, selec);


    fflush(stdout);

    // LOGIC end

    pfree(hist_lower1);
    pfree(hist_upper1);
    pfree(hist_lower2);
    pfree(hist_upper2);

    free_attstatsslot(&sslot1);
    free_attstatsslot(&sslot2);

    ReleaseVariableStats(vardata1);
    ReleaseVariableStats(vardata2);

    CLAMP_PROBABILITY(selec);
    PG_RETURN_FLOAT8((float8) selec);
}

/*
 * Selectivity for operators that depend on area, such as "overlap".
 */

Datum
areasel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.005);
}

Datum
areajoinsel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.005);
}

/*
 *	positionsel
 *
 * How likely is a box to be strictly left of (right of, above, below)
 * a given box?
 */

Datum
positionsel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.1);
}

Datum
positionjoinsel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.1);
}

/*
 *	contsel -- How likely is a box to contain (be contained by) a given box?
 *
 * This is a tighter constraint than "overlap", so produce a smaller
 * estimate than areasel does.
 */

Datum
contsel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.001);
}

Datum
contjoinsel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.001);
}
