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
#include <set>
#include <queue>
#include <algorithm>

using  namespace std;
static char ktoc[] = "wlsd";
static char *jtoa[NJmp] = {
  "Jxxx",
#define X(j) #j,
  JMPS(X)
#undef X
};

struct Jmp{
  short type;
  Ref arg;
};

typedef enum Utype{
  UXXX,
  UPhi,
  UIns,
  UJmp,
};

struct UseInfo;

struct BlkInfo
{
  int index;
  Blk * blk;
  //BlkInfo * s1 = NULL;
  //BlkInfo * s2 = NULL;
  //bool * useVar;
  //bool * defVar;
  //bool * outVar;
  set<BlkInfo*> fron;
  set<BlkInfo*> dom;
  set<BlkInfo*> pfron;
  set<BlkInfo*> pdom;

  BlkInfo * idom;
  BlkInfo * pidom;

  BlkInfo ** pred;
  int npred;
  BlkInfo ** succ;
  int nsucc;

  UseInfo * jmp;

  bool marked = false;
  ~BlkInfo()
  {
    //delete[] useVar;
    //delete[] defVar;
    //delete[] outVar;
    delete[] pred;
    delete[] succ;
  }
};



struct TmpInfo
{
  Tmp * tmp;
  UseInfo * def;
};

struct UseInfo
{
  Utype type;
  BlkInfo * blk; //related block        
  union {
    Ins * ins;   
    Phi * phi;
    Jmp * jmp;   
  } u;
  bool marked;
  TmpInfo *  def; //defined var
  TmpInfo ** use; //used var
  int   nuse;
  ~UseInfo()
  {
    delete[] use;
  }
};


struct FnInfo
{
  Fn * fn;
  BlkInfo * blkArr;
  UseInfo * useArr;
  TmpInfo * tmpArr;
  int nuse;
  int * idMap;
  ~FnInfo()
  {
    delete[] idMap;
    delete[] blkArr;
    delete[] useArr;
    delete[] tmpArr;
  }
};

static void reverse(int blkAmount, BlkInfo* blkArr)
{
  int tempInt;
  BlkInfo ** tempRef;
  bool * tempArr;
  for (int i = 0; i < blkAmount; ++i)
  {
    swap(blkArr[i].pred, blkArr[i].succ);
    swap(blkArr[i].npred, blkArr[i].nsucc);

    blkArr[i].dom.swap( blkArr[i].pdom);
    blkArr[i].fron.swap( blkArr[i].pfron);

    swap(blkArr[i].idom, blkArr[i].pidom);
  }
}

static bool critical(Ins* i) {
  return isstore(i->op) || isarg(i->op);
}

static Blk * findBlkById(int id, Fn * fn)
{
  for (Blk *blk = fn->start; blk; blk = blk->link) 
  {
    if(blk->id == id)
      return blk;
  }
  return NULL;
}

static void printIns(Fn * fn, Ins * i)
{
  if (!req(i->to, R)) {
    printref(i->to, fn, stdout);
    printf(" =%c ", ktoc[i->cls]);
  }
  printf("%s", optab[i->op].name);
  if (req(i->to, R))
    switch (i->op) {
      case Oarg:
      case Oswap:
      case Oxcmp:
      case Oacmp:
      case Oacmn:
      case Oafcmp:
      case Oxtest:
      case Oxdiv:
      case Oxidiv:
      fputc(ktoc[i->cls], stdout);
    }
  if (!req(i->arg[0], R)) {
    printf(" ");
    printref(i->arg[0], fn, stdout);
  }
  if (!req(i->arg[1], R)) {
    printf(", ");
    printref(i->arg[1], fn, stdout);
  }
  printf("\n");
}

static void printPhi(Fn * fn, Phi * p)
{
  printref(p->to, fn, stdout);
  printf(" =%c phi ", ktoc[p->cls]);
  
  for (int n=0;; n++) {
    printf("@%s ", p->blk[n]->name);
    printref(p->arg[n], fn, stdout);
    if (n == p->narg-1) {
      printf("\n");
      break;
    } else
      printf(", ");
  }
}

static void printJmp(Fn * fn, Blk * b)
{
  switch (b->jmp.type) {
  case Jret0:
  case Jretw:
  case Jretl:
  case Jrets:
  case Jretd:
  case Jretc:
    printf( "%s", jtoa[b->jmp.type]);
    if (b->jmp.type != Jret0 || !req(b->jmp.arg, R)) {
        printf( " ");
        printref(b->jmp.arg, fn, stdout);
    }
    if (b->jmp.type == Jretc)
        printf(", :%s", typ[fn->retty].name);
    printf("\n");
    break;
  case Jjmp:
    //if (b->s1 != b->link)
        printf("jmp @%s\n", b->s1->name);
    break;
  default:
    printf( "%s ", jtoa[b->jmp.type]);
    if (b->jmp.type == Jjnz) {
        printref(b->jmp.arg, fn, stdout);
        printf(", ");
    }
    printf("@%s, @%s\n", b->s1->name, b->s2->name);
    break;
  }
}

static void printUseInfo(Fn * fn, UseInfo * use)
{  
  if(use->type == UPhi)
    printPhi(fn,use->u.phi);
  if(use->type == UIns)
    printIns(fn,use->u.ins);
  if(use->type == UJmp)
    printJmp(fn, use->blk->blk);
}

static int ifVarThenIndx(Ref r)
{
  if(r.type == RTmp &&  r.val - Tmp0 >=0)
    return r.val;
  return -1;
}

static void fillDomFront(Fn *fn, BlkInfo* blkArr)
{
  for (int i = 0; i < fn->nblk; ++i)
  {
    if (blkArr[i].npred > 1)    
      for (int j = 0; j < blkArr[i].npred; ++j)
      {
        BlkInfo * ref = blkArr[i].pred[j];
        while(ref != blkArr[i].idom)
        {
          ref->fron.insert(blkArr+i);
          ref = ref->idom;
        }
      }    
  }
}

static bool isIdom(int i, int j, BlkInfo* blkArr)
{
    blkArr[i].dom.erase(blkArr+i);
    bool flag = i != j && blkArr[i].dom == blkArr[j].dom;
    blkArr[i].dom.insert(blkArr+i);
    return flag;
}

static void fillDom(Fn *fn, BlkInfo* blkArr)
{
  bool changed; 
  int blkAmount = fn->nblk;
  do{

    changed = false;
    for (int i = 0; i < fn->nblk; ++i)
    {
      if(blkArr[i].npred == 0)
        continue;

      set<BlkInfo*> temp2 = set<BlkInfo*>();
      for(int k = 0; k < blkAmount; ++k)
        temp2.insert(blkArr+k);

      for (int j = 0; j < blkArr[i].npred; ++j)
      {
        set<BlkInfo*> temp = blkArr[i].pred[j]->dom, temp3;
        temp.insert( blkArr[i].pred[j]);
        set_intersection( temp2.begin(), temp2.end(),temp.begin(), temp.end(), inserter(temp3, temp3.begin()));
        temp2 = temp3;
      }

      temp2.insert(blkArr+i);

      if(blkArr[i].dom != temp2)      
      {
        blkArr[i].dom = temp2;
        changed = true;
      }  
    }
  } while(changed);

  for (int i = 0; i < blkAmount; ++i)
  {
    if(blkArr[i].npred == 1)
      blkArr[i].idom = blkArr[i].pred[0];
    else for (int j = 0; j < blkAmount; ++j)        
      if(blkArr[i].dom.find(blkArr+j) != blkArr[i].dom.end() && isIdom(i,j, blkArr))
      {
        blkArr[i].idom = blkArr + j;
        break;
      } 
  } 
}


static int countPhi(Phi * phi)
{
  int n = 0;
  while(phi != NULL)
  {
    phi = phi->link;
    n++;
  }
  return n;
}


//also computes total amont of meaningful commands:
//nphi + nins + njmp
static void initBlkInfo(FnInfo * fni) 
{
  Fn * fn = fni->fn;
  BlkInfo * blkArr = fni->blkArr;

  int j =0, blkAmount = fn->nblk;
  uint * idMap = new uint[fn->nblk];
  int total = fn->nblk;

  for (Blk *blk = fn->start; blk; blk = blk->link,j++) 
  {
    total+= blk->nins + countPhi(blk->phi);
    blkArr[j].index = j;
    blkArr[j].idom = NULL;
    blkArr[j].blk = blk;

    blkArr[j].npred = blk->npred;
    blkArr[j].pred = new BlkInfo*[blk->npred];

    blkArr[j].nsucc = (blk->s1 != NULL) + (blk->s2 != NULL);
    blkArr[j].succ = new BlkInfo*[blkArr[j].nsucc];

    blkArr[j].fron = set<BlkInfo*>();
    blkArr[j].dom = set<BlkInfo*>();

    blkArr[j].pfron = set<BlkInfo*>();
    blkArr[j].pdom = set<BlkInfo*>();

    if(blkArr[j].npred == 0)
      blkArr[j].dom.insert(blkArr+j);
    else
      for(int k = 0; k < blkAmount; ++k)
        blkArr[j].dom.insert(blkArr+k);

    if(blkArr[j].nsucc == 0)
      blkArr[j].pdom.insert(blkArr+j);
    else
      for(int k = 0; k < blkAmount; ++k)
        blkArr[j].pdom.insert(blkArr+k);

    idMap[blk->id] = j;
  }
  
  for (int i = 0; i < blkAmount; ++i)
  {
    for (int j = 0; j < blkArr[i].npred; ++j)
      blkArr[i].pred[j] = blkArr + idMap[ blkArr[i].blk->pred[j]->id];

    if(blkArr[i].nsucc > 0)
      blkArr[i].succ[0] = blkArr + idMap[ blkArr[i].blk->s1->id];
    if(blkArr[i].nsucc > 1)
      blkArr[i].succ[1] = blkArr + idMap[ blkArr[i].blk->s2->id];
  }

  fni->nuse = total;
}

static void initUseInfo(FnInfo * fni) 
{
  Fn * fn = fni->fn;
  BlkInfo * blkArr = fni->blkArr;
  UseInfo * useArr = fni->useArr;
  TmpInfo * tmpArr = new TmpInfo[fn->ntmp - Tmp0];
  fni->tmpArr = tmpArr;
  for (int i = 0; i < fn->ntmp - Tmp0; ++i)
    tmpArr[i].tmp = fn->tmp + i + Tmp0;

  int i =0, n = 0;
  for (int n = 0; n < fn->nblk; ++i,++n) 
  {
    Blk * blk  = blkArr[n].blk;
    for(Phi *phi = blk->phi; phi; phi = phi->link,i++)
    {
      useArr[i].type = UPhi;
      useArr[i].blk = blkArr + n;
      useArr[i].u.phi = phi;
      useArr[i].marked = false;
      useArr[i].def = tmpArr + phi->to.val - Tmp0;
      tmpArr[phi->to.val - Tmp0].def = useArr + i;
      useArr[i].nuse = phi->narg;
      useArr[i].use = new TmpInfo*[phi->narg];
      for (int j = 0; j < phi->narg; ++j)      
        useArr[i].use[j] = tmpArr + phi->arg[j].val - Tmp0;
    }

    int j =0;
    for (Ins *ins = blk->ins; j < blk->nins; j++, i++, ins++)
    {
      int varTo = ifVarThenIndx(ins->to),
      var0 = ifVarThenIndx(ins->arg[0]), 
      var1 = ifVarThenIndx(ins->arg[1]),
      v = 0;

      useArr[i].type = UIns;
      useArr[i].blk = blkArr + n;
      useArr[i].u.ins = ins;
      useArr[i].marked = critical(ins);
      useArr[i].def = varTo > 0 ? tmpArr + varTo - Tmp0: NULL;

      useArr[i].nuse = (var0 > 0) + (var1 > 0);
      useArr[i].use = new TmpInfo*[useArr[i].nuse];
      if(var0 > 0)
        useArr[i].use[v++]= tmpArr + var0 - Tmp0;
      if(var1 > 0)
        useArr[i].use[v++]= tmpArr + var1 - Tmp0;
      if(varTo > 0)
        tmpArr[varTo - Tmp0].def = useArr + i;
    }

    int varRet = ifVarThenIndx(blk->jmp.arg);
    useArr[i].type = UJmp;
    useArr[i].blk = blkArr + n;
    useArr[i].u.jmp = (Jmp*) &blk->jmp;
    useArr[i].marked = isret( blk->jmp.type );
    useArr[i].def = NULL;
    useArr[i].nuse = (varRet>0);
    useArr[i].use = new TmpInfo*[varRet>0];
    if(varRet>0)
      useArr[i].use[0]= tmpArr + varRet - Tmp0;
    blkArr[n].jmp = useArr + i;
  }
}

static void deletePhi(UseInfo * use)
{

  Phi * prev = use->blk->blk->phi;
  if(use->u.phi == prev)
  {
    use->blk->blk->phi = use->blk->blk->phi->link;
    return;
  }

  for (Phi * p = prev -> link; p; p = p->link, prev = prev->link)
  {
    if(use->u.phi == p)
    {
      prev->link = p->link;
      return;
    }
  }

}

static void mark(FnInfo * fni)
{
  queue<UseInfo*> workList = queue<UseInfo*>();
  UseInfo * useArr = fni->useArr;
  for (int i = 0; i < fni->nuse; ++i)
    if(useArr[i].marked)
    {
      workList.push(useArr+i);
      useArr[i].blk->marked = true;
    }
  while(workList.size()>0)
  {
    UseInfo * use = workList.front();
    workList.pop();

    for (int i = 0; i < use->nuse; ++i)
      if(!use->use[i]->def->marked)
      {
        use->use[i]->def->marked = true;
        workList.push(use->use[i]->def);
        use->blk->marked = true;
      }
    
    if(use->type == UPhi)    
      for (int i = 0; i < use->blk->npred; ++i)
      {
        use->blk->pred[i]->jmp->marked = true;
        use->blk->pred[i]->marked = true;
        workList.push(use->blk->pred[i]->jmp);
      }
    

    for(auto iter = use->blk->pfron.begin(); iter != use->blk->pfron.end(); iter++)
    {
      UseInfo * jmp = (*iter)->jmp;
      if(!jmp->marked)
      {
        jmp->marked = true;
        workList.push(jmp);
        use->blk->marked = true;
      }
    }
  }
}

static void sweep(FnInfo * fni)
{
  UseInfo * useArr = fni->useArr;
  for (int i = 0; i < fni->nuse; ++i)
  {
    if(!useArr[i].marked && useArr[i].type == UIns)
    {
      useArr[i].u.ins->op = Onop;
      useArr[i].u.ins->to = R;
      useArr[i].u.ins->arg[0] = R;
      useArr[i].u.ins->arg[1] = R;
    }

    if(!useArr[i].marked && useArr[i].type == UPhi)
      deletePhi(useArr+i);
    if(!useArr[i].marked && useArr[i].type == UJmp)
      if(useArr[i].u.jmp->type > Jjmp) //if it's a branch
      {
        BlkInfo * p = useArr[i].blk->pidom;
        while(!p->marked)
          p = p->pidom;
        useArr[i].blk->blk->s1 = p->blk;
        useArr[i].blk->blk->s2 = NULL;
        useArr[i].u.jmp->type = Jjmp;
      }
  }
}

static void readfn (Fn *fn) {

  fillrpo(fn); // Traverses the CFG in reverse post-order, filling blk->id.
  fillpreds(fn);
  filluse(fn);
  ssa(fn);
  filluse(fn);  
  int blkAmount = fn->nblk, varAmount = fn->ntmp - Tmp0,j=0;

  FnInfo * fni = new FnInfo;
  fni->fn = fn;

  BlkInfo * blkArr = new BlkInfo[blkAmount];
  fni->blkArr = blkArr;
  initBlkInfo(fni);

  
  fillDom(fn, blkArr); 
  fillDomFront(fn, blkArr);

  reverse(blkAmount, blkArr);
  fillDom(fn, blkArr);
  fillDomFront(fn, blkArr);
  reverse(blkAmount, blkArr); 

  UseInfo * useArr = new UseInfo[fni->nuse];
  fni->useArr = useArr;
  initUseInfo(fni);
  mark(fni);

  /*
  for (int j = 0; j < blkAmount; ++j)
  {
    printf("@%s(id: %d)\n", blkArr[j].blk->name, blkArr[j].blk->id);


    printf("pred:");
    for (int i = 0; i < blkArr[j].npred; ++i)
       printf(" @%s", blkArr[j].pred[i]->blk->name);
    printf("\n");

    printf("succ:");
    for (int i = 0; i < blkArr[j].nsucc; ++i)
       printf(" @%s", blkArr[j].succ[i]->blk->name);
    printf("\n");
    printf("\n");

    printf("  idom is: @%s\n", (blkArr[j].idom != NULL ) ? blkArr[j].idom->blk->name : "Enter" );   

    printf("  dom is:");
    for (auto iter = blkArr[j].dom.begin(); iter != blkArr[j].dom.end(); iter++)
       printf(" @%s", (*iter)->blk->name);
    printf("\n");

    printf("  dom front is:");
    for (auto iter = blkArr[j].fron.begin(); iter != blkArr[j].fron.end(); iter++)
       printf(" @%s", (*iter)->blk->name);
    printf("\n");
    printf("\n");
    printf("  post idom is: @%s\n", (blkArr[j].pidom != NULL ) ? blkArr[j].pidom->blk->name : "Exit" );

    printf("  post dom is:");
    for (auto iter = blkArr[j].pdom.begin(); iter != blkArr[j].pdom.end(); iter++)
       printf(" @%s", (*iter)->blk->name);
    printf("\n");
    
    printf("  post dom front is:");
    for (auto iter = blkArr[j].pfron.begin(); iter != blkArr[j].pfron.end(); iter++)
       printf(" @%s", (*iter)->blk->name);
    printf("\n");    
  }

  
  for (int i = 0; i < fni->nuse; ++i)
  {
    if(fni->useArr[i].marked)    
      printf("marked\t");
    printUseInfo(fn,fni->useArr+i);
  }
  */
  sweep(fni);

  fillpreds(fn); // Either call this, or keep track of preds manually when rewriting branches.
  fillrpo(fn); 
  printfn(fn,stdout);

  delete fni;  
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}