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
#include <stack>
#include <queue>
#include <vector>
#include <algorithm>

using namespace std;


struct TmpInfo;
struct PhiInfo
{
  TmpInfo * tmp;
  int ind;
  vector<int> tmpInd;
  PhiInfo(TmpInfo * t,int n)
  {
    ind =0;
    tmp = t;
    tmpInd = vector<int>(n,-1);
  }
};

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
  set<BlkInfo*> rdom;

  BlkInfo * idom;

  BlkInfo ** pred;
  int npred;
  BlkInfo ** succ;
  int nsucc;

  set<TmpInfo*> def;

  vector<PhiInfo*> phies;

  ~BlkInfo()
  {
    //delete[] useVar;
    //delete[] defVar;
    //delete[] outVar;
    delete[] pred;
    delete[] succ;
    for (auto iter = phies.begin(); iter != phies.end(); iter++)
      delete (*iter);
  }
};

struct TmpInfo
{
  Tmp * tmp;
  set<BlkInfo*> blks;
};

struct FnInfo
{
  Fn * fn;
  BlkInfo * blkArr;
  TmpInfo * tmpArr;
  int * idMap;
  ~FnInfo()
  {
    delete[] idMap;
    delete[] blkArr;
    delete[] tmpArr;
  }
};

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
    if(blkArr[i].idom)
      blkArr[i].idom->rdom.insert(blkArr+i);
  } 
}




static void initBlkInfo(FnInfo * fni) 
{
  Fn * fn = fni->fn;
  BlkInfo * blkArr = fni->blkArr;

  int j =0, blkAmount = fn->nblk;
  uint * idMap = new uint[fn->nblk];
  int total = fn->nblk;

  for (Blk *blk = fn->start; blk; blk = blk->link,j++) 
  {
    blkArr[j].index = j;
    blkArr[j].idom = NULL;
    blkArr[j].blk = blk;

    blkArr[j].npred = blk->npred;
    blkArr[j].pred = new BlkInfo*[blk->npred];

    blkArr[j].nsucc = (blk->s1 != NULL) + (blk->s2 != NULL);
    blkArr[j].succ = new BlkInfo*[blkArr[j].nsucc];

    blkArr[j].fron = set<BlkInfo*>();
    blkArr[j].dom = set<BlkInfo*>();
    blkArr[j].rdom = set<BlkInfo*>();

    blkArr[j].def = set<TmpInfo*>();

    blkArr[j].phies = vector<PhiInfo*>();

    if(blkArr[j].npred == 0)
      blkArr[j].dom.insert(blkArr+j);
    else
      for(int k = 0; k < blkAmount; ++k)
        blkArr[j].dom.insert(blkArr+k);

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
}


void initTmpInfo(FnInfo * fni)
{
  Fn * fn = fni->fn;
  BlkInfo * blkArr = fni->blkArr;
  TmpInfo * tmpArr = fni->tmpArr;
  for (int i = 0; i < fn->ntmp - Tmp0; ++i)
  {
    tmpArr[i].blks = set<BlkInfo*>();
    tmpArr[i].tmp = fn->tmp + i + Tmp0;
  }

  for (int n = 0; n < fn->nblk; ++n) 
  {
    Blk * blk  = blkArr[n].blk;
    int j = 0;
    for (Ins *ins = blk->ins; j < blk->nins; j++, ins++)
    {
      int varTo = ifVarThenIndx(ins->to);

      if(varTo > 0)
      {
        tmpArr[varTo - Tmp0].blks.insert(blkArr + n);
        blkArr[n].def.insert(tmpArr + varTo - Tmp0);
      }
    }
  }
}

void placePhi(FnInfo * fni)
{
  Fn * fn = fni->fn;
  BlkInfo * blkArr = fni->blkArr;
  TmpInfo * tmpArr = fni->tmpArr;
  int varAmount = fn->ntmp - Tmp0;

  set<BlkInfo*> workList = set<BlkInfo*>();
  for (int i = 0; i < varAmount; ++i)
  {
    workList = tmpArr[i].blks;
    set<BlkInfo*> placed = set<BlkInfo*>();
    while(workList.size()>0)
    {
      BlkInfo * b = *workList.begin();
      for (auto iter2 = b->fron.begin(); iter2 != b->fron.end(); iter2++)
      {
        BlkInfo * d = *iter2;
        if(placed.find(d) != placed.end())
           continue;
        PhiInfo * np = new PhiInfo( tmpArr+i, d->npred);
        d->phies.push_back(np);

        workList.insert(d);
        placed.insert(d);
      }
      workList.erase(b);
    }
  }
}

int counter;
vector<stack<int>> vstack;
int newName(int n)
{
  
  int i = counter;
  counter++;
  vstack[n].push(i);
  return i;
}

void renamePhi(FnInfo * fni, int n)
{
  BlkInfo * blkArr = fni->blkArr;
  TmpInfo * tmpArr = fni->tmpArr;

  int varAmount = fni->fn->ntmp - Tmp0;
  BlkInfo * b = blkArr + n;
  for (auto iter = b->phies.begin(); iter != b->phies.end(); iter++)
    (*iter)->ind = newName((*iter)->tmp - tmpArr); // substitute for index

  int j = 0;
  for (Ins *ins = b->blk->ins; j < b->blk->nins; j++, ins++)
  {
    int varTo = ifVarThenIndx(ins->to);
    if(varTo > 0)
      newName(varTo - Tmp0);
  }


  for (int i = 0; i < b->nsucc; ++i)
  {
    for (int j = 0; j < b->succ[i]->npred; ++j)
    {
      if(b->succ[i]->pred[j] == b) //
        for(auto iter = b->succ[i]->phies.begin(); iter != b->succ[i]->phies.end(); iter++)
        {
          (*iter)->tmpInd[j] = vstack[ (*iter)->tmp - tmpArr ].top();
        }
    }    
  }

  for(auto iter = b->rdom.begin(); iter != b->rdom.end(); iter++)  
    renamePhi(fni, (*iter)->index);

  for (auto iter = b->phies.begin(); iter != b->phies.end(); iter++)
    vstack[(*iter)->tmp - tmpArr].pop();

  j = 0;
  for (Ins *ins = b->blk->ins; j < b->blk->nins; j++, ins++)
  {
    int varTo = ifVarThenIndx(ins->to);
    if(varTo > 0)
      vstack[varTo - Tmp0].pop();
  }
  
}

void namePhi(FnInfo * fni)
{
  counter = 1;
  vstack = vector<stack<int>>(fni->fn->ntmp - Tmp0);
  for (int i = 0; i < fni->fn->ntmp - Tmp0; ++i)
  {
    vstack[i].push(-1);
  }
  renamePhi(fni, 0);
}

static void readfn (Fn *fn) {

  int blkAmount = fn->nblk, varAmount = fn->ntmp - Tmp0;

  FnInfo * fni = new FnInfo;
  fni->fn = fn;
  
  fni->blkArr = new BlkInfo[blkAmount];
  BlkInfo * blkArr = fni->blkArr;

  fni->tmpArr = new TmpInfo[varAmount];
  TmpInfo * tmpArr = fni->tmpArr;

  initBlkInfo(fni);

  fillDom(fn, blkArr);
  fillDomFront(fn, blkArr);


  initTmpInfo(fni);
  placePhi(fni);
  namePhi(fni);

  for (int j = 0; j < blkAmount; ++j)
  {
    printf("@%s:\n", blkArr[j].blk->name, blkArr[j].blk->id);
    for (auto iter = blkArr[j].phies.begin(); iter != blkArr[j].phies.end(); iter++)
    {
      printf("  %%%s %d =", (*iter)->tmp->tmp->name,(*iter)->ind );
      for (int i = 0; i < blkArr[j].npred; ++i)
      {
        printf(" @%s %d",blkArr[j].pred[i]->blk->name,(*iter)->tmpInd[i]);
      }
      printf("\n");

    }
    //    printf(" @%s", (*iter)->blk->name);

    // printf("pred:");
    // for (int i = 0; i < blkArr[j].npred; ++i)
    //    printf(" @%s", blkArr[j].pred[i]->blk->name);
    // printf("\n");

    // printf("succ:");
    // for (int i = 0; i < blkArr[j].nsucc; ++i)
    //    printf(" @%s", blkArr[j].succ[i]->blk->name);
    // printf("\n");
    // printf("\n");

    // printf("  idom is: @%s\n", (blkArr[j].idom != NULL ) ? blkArr[j].idom->blk->name : "Enter" );   

    // printf("  dom is:");
    // for (auto iter = blkArr[j].dom.begin(); iter != blkArr[j].dom.end(); iter++)
    //    printf(" @%s", (*iter)->blk->name);
    // printf("\n");

    // printf("  dom front is:");
    // for (auto iter = blkArr[j].fron.begin(); iter != blkArr[j].fron.end(); iter++)
    //    printf(" @%s", (*iter)->blk->name);
    // printf("\n");

    //     printf("  rdom is:");
    // for (auto iter = blkArr[j].rdom.begin(); iter != blkArr[j].rdom.end(); iter++)
    //    printf(" @%s", (*iter)->blk->name);
    // printf("\n");

    //     printf("def is:");
    // for (auto iter = blkArr[j].def.begin(); iter != blkArr[j].def.end(); iter++)
    //    printf(" %%%s", (*iter)->tmp->name);
    // printf("\n");
  }
 
  //delete fni;  
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}