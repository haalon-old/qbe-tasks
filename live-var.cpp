#ifdef __cplusplus
#define export exports
extern "C" {
#include "qbe/all.h"
}
#undef export
#else
#include "qbe/all.h"
#endif

#include <stdio.h>

struct BlkInfo
{
  Blk * blk;
  BlkInfo * s1 = NULL;
  BlkInfo * s2 = NULL;
  bool * useVar;
  bool * defVar;
  bool * outVar;

  ~BlkInfo()
  {
    delete[] useVar;
    delete[] defVar;
    delete[] outVar;
  }
};

static void clear(int n, bool * ptr)
{
  for (int i = 0; i < n; ++i)
  {
    *(ptr+i) = false;
  }
}

static int ifVarThenIndx(Ref r)
{
  if(r.type == RTmp &&  r.val - Tmp0 >=0)
    return r.val - Tmp0;
  return -1;
}

static void unite(int n, bool* arr1, bool* arr2, bool* result)
{
  for (int i = 0; i < n; ++i)  
    result[i] = arr1[i] || arr2[i];  
}

static void deduct(int n, bool* arr1, bool* arr2, bool* result)
{
  for (int i = 0; i < n; ++i)  
    result[i] = arr1[i] && !arr2[i];
}

static bool equal(int n, bool* arr1, bool* arr2)
{
  for (int i = 0; i < n; ++i)  
    if(arr1[i] != arr2[i])
      return false;

  return true;
}

static void printVar(Fn* fn , bool * mask)
{
    for (int j = 0; j < fn->ntmp - Tmp0; ++j)
    {
      if(mask[j])
        printf(" %%%s", fn->tmp[j+Tmp0].name);
    }
}

static bool isFinal(Blk* blk)
{ return (blk->s1 == NULL) && (blk->s2 == NULL); }

static void readfn (Fn *fn) {

  BlkInfo* blkArr = new BlkInfo[fn->nblk];
  int varAmount = fn->ntmp - Tmp0;
  int j =0;
  uint * idMap = new uint[fn->nblk];

  for (Blk *blk = fn->start; blk; blk = blk->link,j++) 
  {
    blkArr[j].blk = blk;

    bool * defVar = new bool[varAmount];
    bool * useVar = new bool[varAmount];

    clear(varAmount, defVar);
    clear(varAmount, useVar);

    int i =0;  
    for ( Ins *insarr = blk->ins; i < blk->nins; i++, insarr++)
    {
      int varTo = ifVarThenIndx(insarr->to),
      var0 = ifVarThenIndx(insarr->arg[0]), 
      var1 = ifVarThenIndx(insarr->arg[1]);

      if(var0 >= 0 && !defVar[var0])
        useVar[var0] = true;

      if(var1 >= 0 && !defVar[var1])
        useVar[var1] = true;

      if(varTo >= 0)        
        defVar[varTo]=true;      
    }
    
    if (isFinal(blk) && (blk->jmp.type == 2)  && (blk->jmp.arg.type == RTmp)) 
    {
      if(!defVar[blk->jmp.arg.val-Tmp0])
        useVar[blk->jmp.arg.val-Tmp0]=true;
    }

    blkArr[j].useVar = useVar;
    blkArr[j].defVar = defVar;

    blkArr[j].outVar = new bool[varAmount];
    clear(varAmount, blkArr[j].outVar);

    idMap[blk->id] = j;

  }

  for (int i = 0; i < fn->nblk; ++i)
  {
    if(blkArr[i].blk->s1 != NULL)
      blkArr[i].s1 = blkArr+idMap[blkArr[i].blk->s1->id];
    if(blkArr[i].blk->s2 != NULL)
      blkArr[i].s2 = blkArr+idMap[blkArr[i].blk->s2->id];
  }
  bool changed;
  do{

    changed = false;
    for (int i = 0; i < fn->nblk; ++i)
    {
      bool * outNew = new bool[varAmount];
      bool * temp = new bool[varAmount];
      if(blkArr[i].s1 != NULL)
      {
        deduct(varAmount,blkArr[i].s1->outVar,blkArr[i].s1->defVar, temp);
        unite(varAmount,blkArr[i].s1->useVar,temp,outNew);
      }

      if(blkArr[i].s2 != NULL)
      {
        deduct(varAmount,blkArr[i].s2->outVar,blkArr[i].s2->defVar, temp);
        unite(varAmount,blkArr[i].s2->useVar,temp,temp);
        unite(varAmount,temp,outNew,outNew);
      }

      if(equal(varAmount,blkArr[i].outVar,outNew) || isFinal(blkArr[i].blk))      
        delete[] outNew;      
      else
      {
        blkArr[i].outVar = outNew;
        changed = true;
      }

      delete[] temp;
    }
  } while(changed);

  for (int j = 0; j < fn->nblk; ++j)
  {
    printf("@%s\n", blkArr[j].blk->name);
    
    printf("\tlv_out =");
    printVar(fn, blkArr[j].outVar);

    printf("\n\n");
  }

  delete[] blkArr;  
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}