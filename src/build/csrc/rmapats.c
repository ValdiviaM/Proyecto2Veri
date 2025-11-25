// file = 0; split type = patterns; threshold = 100000; total count = 0.
#include <stdio.h>
#include <stdlib.h>
#include <strings.h>
#include "rmapats.h"

void  hsG_0__0 (struct dummyq_struct * I1353, EBLK  * I1348, U  I707);
void  hsG_0__0 (struct dummyq_struct * I1353, EBLK  * I1348, U  I707)
{
    U  I1613;
    U  I1614;
    U  I1615;
    struct futq * I1616;
    struct dummyq_struct * pQ = I1353;
    I1613 = ((U )vcs_clocks) + I707;
    I1615 = I1613 & ((1 << fHashTableSize) - 1);
    I1348->I752 = (EBLK  *)(-1);
    I1348->I753 = I1613;
    if (0 && rmaProfEvtProp) {
        vcs_simpSetEBlkEvtID(I1348);
    }
    if (I1613 < (U )vcs_clocks) {
        I1614 = ((U  *)&vcs_clocks)[1];
        sched_millenium(pQ, I1348, I1614 + 1, I1613);
    }
    else if ((peblkFutQ1Head != ((void *)0)) && (I707 == 1)) {
        I1348->I755 = (struct eblk *)peblkFutQ1Tail;
        peblkFutQ1Tail->I752 = I1348;
        peblkFutQ1Tail = I1348;
    }
    else if ((I1616 = pQ->I1256[I1615].I775)) {
        I1348->I755 = (struct eblk *)I1616->I773;
        I1616->I773->I752 = (RP )I1348;
        I1616->I773 = (RmaEblk  *)I1348;
    }
    else {
        sched_hsopt(pQ, I1348, I1613);
    }
}
void  hs_0_M_27_0__simv_daidir (UB  * pcode, scalar  val)
{
    UB  * I1680;
    *(pcode + 0) = val;
    RmaRtlXEdgesHdr  * I977 = (RmaRtlXEdgesHdr  *)(pcode + 8);
    RmaRtlEdgeBlock  * I811;
    U  I5 = I977->I5;
    scalar  I843 = (((I5) >> (16)) & ((1 << (8)) - 1));
    US  I1495 = (1 << (((I843) << 2) + (X4val[val])));
    if (I1495 & 31692) {
        rmaSchedRtlXEdges(I977, I1495, X4val[val]);
    }
    (I5) = (((I5) & ~(((U )((1 << (8)) - 1)) << (16))) | ((X4val[val]) << (16)));
    I977->I5 = I5;
    {
        unsigned long long * I1737 = derivedClk + (4U * X4val[val]);
        memcpy(pcode + 104 + 4, I1737, 25U);
    }
    {
        scalar  I1571;
        scalar  I1483;
        U  I1528;
        U  I1579;
        U  I1580;
        EBLK  * I1348;
        struct dummyq_struct * pQ;
        U  I1351;
        I1351 = 0;
        pQ = (struct dummyq_struct *)ref_vcs_clocks;
        I1483 = X4val[val];
        I1571 = *(pcode + 133);
        *(pcode + 133) = I1483;
        I1528 = (I1571 << 2) + I1483;
        I1528 = 1 << I1528;
        if (I1528 & 2) {
            if (getCurSchedRegion()) {
                SchedSemiLerTBReactiveRegion_th((struct eblk *)(pcode + 136), I1351);
            }
            else {
                sched0_th(pQ, (EBLK  *)(pcode + 136));
            }
        }
    }
    {
        scalar  I1361;
        I1361 = val;
        pcode += 176;
        (*(FP  *)(pcode + 0))(*(UB  **)(pcode + 8), I1361);
    }
}
void  hs_0_M_27_5__simv_daidir (UB  * pcode, UB  val)
{
    val = *(pcode + 0);
    *(pcode + 0) = 0xff;
    hs_0_M_27_0__simv_daidir(pcode, val);
}
void  hs_0_M_29_0__simv_daidir (UB  * pcode, scalar  val)
{
    UB  * I1680;
    *(pcode + 0) = val;
    RmaRtlXEdgesHdr  * I977 = (RmaRtlXEdgesHdr  *)(pcode + 8);
    RmaRtlEdgeBlock  * I811;
    U  I5 = I977->I5;
    scalar  I843 = (((I5) >> (16)) & ((1 << (8)) - 1));
    US  I1495 = (1 << (((I843) << 2) + (X4val[val])));
    if (I1495 & 31692) {
        rmaSchedRtlXEdges(I977, I1495, X4val[val]);
    }
    (I5) = (((I5) & ~(((U )((1 << (8)) - 1)) << (16))) | ((X4val[val]) << (16)));
    I977->I5 = I5;
    {
        unsigned long long * I1737 = derivedClk + (4U * X4val[val]);
        memcpy(pcode + 104 + 4, I1737, 25U);
    }
    {
        scalar  I1571;
        scalar  I1483;
        U  I1528;
        U  I1579;
        U  I1580;
        EBLK  * I1348;
        struct dummyq_struct * pQ;
        U  I1351;
        I1351 = 0;
        pQ = (struct dummyq_struct *)ref_vcs_clocks;
        I1483 = X4val[val];
        I1571 = *(pcode + 133);
        *(pcode + 133) = I1483;
        I1528 = (I1571 << 2) + I1483;
        I1528 = 1 << I1528;
        if (I1528 & 2) {
            if (getCurSchedRegion()) {
                SchedSemiLerTBReactiveRegion_th((struct eblk *)(pcode + 136), I1351);
            }
            else {
                sched0_th(pQ, (EBLK  *)(pcode + 136));
            }
        }
    }
}
void  hs_0_M_29_5__simv_daidir (UB  * pcode, UB  val)
{
    val = *(pcode + 0);
    *(pcode + 0) = 0xff;
    hs_0_M_29_0__simv_daidir(pcode, val);
}
void  hs_0_M_38_0__simv_daidir (UB  * pcode, scalar  val)
{
    UB  * I1680;
    *(pcode + 0) = val;
    RmaRtlXEdgesHdr  * I977 = (RmaRtlXEdgesHdr  *)(pcode + 8);
    RmaRtlEdgeBlock  * I811;
    U  I5 = I977->I5;
    scalar  I843 = (((I5) >> (16)) & ((1 << (8)) - 1));
    US  I1495 = (1 << (((I843) << 2) + (X4val[val])));
    if (I1495 & 31692) {
        rmaSchedRtlXEdges(I977, I1495, X4val[val]);
    }
    (I5) = (((I5) & ~(((U )((1 << (8)) - 1)) << (16))) | ((X4val[val]) << (16)));
    I977->I5 = I5;
    {
        unsigned long long * I1737 = derivedClk + (4U * X4val[val]);
        memcpy(pcode + 104 + 4, I1737, 25U);
    }
    {
        scalar  I1571;
        scalar  I1483;
        U  I1528;
        U  I1579;
        U  I1580;
        EBLK  * I1348;
        struct dummyq_struct * pQ;
        U  I1351;
        I1351 = 0;
        pQ = (struct dummyq_struct *)ref_vcs_clocks;
        I1483 = X4val[val];
        I1571 = *(pcode + 133);
        *(pcode + 133) = I1483;
        I1528 = (I1571 << 2) + I1483;
        I1528 = 1 << I1528;
        if (I1528 & 2) {
            if (getCurSchedRegion()) {
                SchedSemiLerTBReactiveRegion_th((struct eblk *)(pcode + 136), I1351);
            }
            else {
                sched0_th(pQ, (EBLK  *)(pcode + 136));
            }
        }
        if (I1528 & 16) {
            if (getCurSchedRegion()) {
                SchedSemiLerTBReactiveRegion_th((struct eblk *)(pcode + 176), I1351);
            }
            else {
                sched0_th(pQ, (EBLK  *)(pcode + 176));
            }
        }
    }
    {
        pcode += 216;
        markMasterClkOvaLists(1, *(RP  *)(pcode + 8));
        *((*(UB  **)(pcode + 8)) + 2) = X4val[val];
        {
            (*txpFnPtr)(pcode, 0);
        }
    }
    {
        pcode += 40;
        {
            markMasterClkOvaLists(0, *(RP  *)(pcode + 8));
            *((*(UB  **)(pcode + 8)) + 2) = X4val[val];
            (*txpFnPtr)(pcode, 0);
        }
    }
    {
        scalar  I1739 = X4val[val];
        scalar  I1740 = *(scalar  *)(pcode + 40 + 2U);
        *(scalar  *)(pcode + 40 + 2U) = I1739;
        UB  * I977 = *(UB  **)(pcode + 40 + 8U);
        if (I977) {
            U  I1741 = I1739 * 2;
            U  I1742 = 1 << ((I1740 << 2) + I1739);
            *(pcode + 40 + 0U) = 1;
            while (I977){
                UB  * I1744 = *(UB  **)(I977 + 16U);
                if ((*(US  *)(I977 + 0U)) & I1742) {
                    *(*(UB  **)(I977 + 48U)) = 1;
                    (*(FP  *)(I977 + 32U))((void *)(*(RP  *)(I977 + 40U)), (((*(scalar  *)(I977 + 2U)) >> I1741) & 3));
                }
                I977 = I1744;
            };
            *(pcode + 40 + 0U) = 0;
            rmaRemoveNonEdgeLoads(pcode + 40);
        }
    }
    {
        scalar  I1361;
        I1361 = val;
        (*(FP  *)(pcode + 80))(*(UB  **)(pcode + 88), I1361);
        (*(FP  *)(pcode + 96))(*(UB  **)(pcode + 104), I1361);
        (*(FP  *)(pcode + 112))(*(UB  **)(pcode + 120), I1361);
        pcode += 128;
        (*(FP  *)(pcode + 0))(*(UB  **)(pcode + 8), I1361);
        (*(FP  *)(pcode + 16))(*(UB  **)(pcode + 24), I1361);
        (*(FP  *)(pcode + 32))(*(UB  **)(pcode + 40), I1361);
        (*(FP  *)(pcode + 48))(*(UB  **)(pcode + 56), I1361);
        (*(FP  *)(pcode + 64))(*(UB  **)(pcode + 72), I1361);
        (*(FP  *)(pcode + 80))(*(UB  **)(pcode + 88), I1361);
        (*(FP  *)(pcode + 96))(*(UB  **)(pcode + 104), I1361);
        (*(FP  *)(pcode + 112))(*(UB  **)(pcode + 120), I1361);
        pcode += 128;
        (*(FP  *)(pcode + 0))(*(UB  **)(pcode + 8), I1361);
        (*(FP  *)(pcode + 16))(*(UB  **)(pcode + 24), I1361);
        (*(FP  *)(pcode + 32))(*(UB  **)(pcode + 40), I1361);
        (*(FP  *)(pcode + 48))(*(UB  **)(pcode + 56), I1361);
        (*(FP  *)(pcode + 64))(*(UB  **)(pcode + 72), I1361);
    }
}
#ifdef __cplusplus
extern "C" {
#endif
void SinitHsimPats(void);
#ifdef __cplusplus
}
#endif
