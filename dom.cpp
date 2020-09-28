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
  int index;
  Blk * blk;
  //BlkInfo * s1 = NULL;
  //BlkInfo * s2 = NULL;
  //bool * useVar;
  //bool * defVar;
  //bool * outVar;
  bool * dom;
  BlkInfo ** pred;
  int npred;


  ~BlkInfo()
  {
    //delete[] useVar;
    //delete[] defVar;
    //delete[] outVar;
    delete[] pred;
    delete[] dom;
  }
};

static void clear(int n, bool * ptr, bool def = false)
{
  for (int i = 0; i < n; ++i)
  {
    *(ptr+i) = def;
  }
}
/*
static int ifVarThenIndx(Ref r)
{
  if(r.type == RTmp &&  r.val - Tmp0 >=0)
    return r.val - Tmp0;
  return -1;
} */

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

static void intersect(int n, bool* arr1, bool* arr2, bool* result)
{
  for (int i = 0; i < n; ++i)  
    result[i] = arr1[i] && arr2[i];
}

static void copy(int n, bool* arr1, bool* result)
{
  for (int i = 0; i < n; ++i)  
    result[i] = arr1[i];
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
  int j =0, blkAmount = fn->nblk;
  uint * idMap = new uint[fn->nblk];

  for (Blk *blk = fn->start; blk; blk = blk->link,j++) 
  {
    blkArr[j].index = j;
    blkArr[j].blk = blk;
    blkArr[j].npred = blk->npred;
    blkArr[j].pred = new  BlkInfo*[blk->npred];
    blkArr[j].dom = new bool[blkAmount];

    if(blk->npred == 0)
    {
      clear(blkAmount, blkArr[j].dom);
      blkArr[j].dom[j] = true;
    }
    else
      clear(blkAmount, blkArr[j].dom,true);
    idMap[blk->id] = j;
  }
  
  for (int i = 0; i < blkAmount; ++i)
  {
    for (int j = 0; j < blkArr[i].npred; ++j)
    {
      blkArr[i].pred[j] = blkArr + idMap[ blkArr[i].blk->pred[j]->id];
    }
  }

  bool changed;
  do{

    changed = false;
    for (int i = 0; i < fn->nblk; ++i)
    {
      if(blkArr[i].npred == 0)
        continue;

      bool * temp = new bool[blkAmount];
      bool * temp2 = new bool[blkAmount];
      clear(blkAmount,temp,true);

      for (int j = 0; j < blkArr[i].npred; ++j)
      {
        copy(blkAmount,blkArr[i].pred[j]->dom,temp2);
        temp2[ blkArr[i].pred[j]->index ] = true;
        intersect(blkAmount, temp2, temp,temp );
      }

      temp[i] = true;

      if(equal(blkAmount,blkArr[i].dom, temp))      
        delete[] temp;      
      else
      {
        blkArr[i].dom = temp;
        changed = true;
      }
      delete[] temp2;  
    }
  } while(changed);

  for (int j = 0; j < fn->nblk; ++j)
  {
    printf("@%s   ", blkArr[j].blk->name);

    for (int i = 0; i < blkAmount; ++i)
        if(blkArr[i].dom[j])
          printf(" @%s", blkArr[i].blk->name);

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