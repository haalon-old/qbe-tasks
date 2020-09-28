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

static void readfn (Fn *fn) {

  //set <uint, greater <uint> > defVar; 
  //set <uint, greater <uint> > useVar; 
  //printf("%d\n",fn->ntmp - Tmp0);
  bool * defVar = new bool[fn->ntmp - Tmp0];
  bool * useVar = new bool[fn->ntmp - Tmp0];

  for (Blk *blk = fn->start; blk; blk = blk->link) {
    printf("@%s\n", blk->name);
    //printf("\n%d %d %s",  (blk->jmp.type),(blk->jmp.arg.type) , fn->tmp[blk->jmp.arg.val].name);

    clear(fn->ntmp - Tmp0, defVar);
    clear(fn->ntmp - Tmp0, useVar);

    int i =0;

    printf("\tdef =");   
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
    
    if ((blk->s1 == NULL) && (blk->s2 == NULL) && (blk->jmp.type == 2)  && (blk->jmp.arg.type == RTmp)) 
    {
      if(!defVar[blk->jmp.arg.val-Tmp0])
        useVar[blk->jmp.arg.val-Tmp0]=true;
    }

    for (int i = 0; i < fn->ntmp - Tmp0; ++i)
    {
      if(defVar[i])
        printf(" %%%s", fn->tmp[i+Tmp0].name); 
    } 

    printf("\n\tuse =");
    for (int i = 0; i < fn->ntmp - Tmp0; ++i)
    {
      if(useVar[i])
        printf(" %%%s", fn->tmp[i+Tmp0].name); 
    } 
    printf("\n\n");   

  }
  delete[] useVar;
  delete[] defVar;
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}