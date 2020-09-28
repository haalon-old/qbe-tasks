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

/**
Вспомогательные функции, введённые для сокращения записи:
**/
#define L_MAX 64
void print_blk_set(char **set) {
    int n = 0;
    while (set[n]!=0){
        printf("%%%s ",set[n]);
        ++n;
    }
}
int is_final_BLK (Blk *blk) {
    return (blk->s1 == NULL) && (blk->s2 == NULL);
}
int is_named_var (Ref *tmp) {
    return tmp->type==RTmp;
}
int check_in (char** where, char* what) {
    for (register int n=0; (n < L_MAX) && (where[n]!=0); ++n) {
        if (where[n]==what) {
            return 1;
        }
    }
    return 0;
}
int add_elem (char ** whither, int* bound_pointer, char* what) {
    whither[*bound_pointer] = what;
    if (*bound_pointer==L_MAX) return -1;
    ++(*bound_pointer);
    whither[*bound_pointer] = 0;
    return 0;
}

int find_pos(Blk **base_blocks, Blk *check_block){
    /** поиск позиции, которую занимает в ряду ББ (base_blocks) заданный ББ (check_block) **/
    for(int i=0;base_blocks[i]!=0;++i)
        if (base_blocks[i]==check_block) return i;
    return -1;
};

void array_union(char **out_live_array, int *out_block_bound, char** in_array){
    /** объединение множеств, изменения накапливаются в (out_live_array), граница (out_block_bound) меняется **/
    int i=0;
    int Flag=0;
    register int limit = *out_block_bound;
    while (in_array[i]!=0){
        Flag=0;
        for (register int j=0; j < limit ;++j){
            if (in_array[i]==out_live_array[j]) {Flag = 1; break;}
        }
        if (!Flag) {
            add_elem(out_live_array, out_block_bound, in_array[i]);
        }
        ++i;
    }
    return;
};

void set_difference(char **out_live_array, int *out_block_bound, char **def_block_array){
    /** разность множеств: из множества (out_live_array) вычитается набор (def_block_array),
    после чего исходное множество (out_live_array) "уплотняется", а его граница сдвигается
    **/
    int i=0;
    int count=0;
    int limit = *out_block_bound;
    while (def_block_array[i]!=0){
        for (register int j=0; j < limit;++j){
            if (def_block_array[i]==out_live_array[j]) {
                ++count;
                out_live_array[j] = 0;
                break;
            }
        }
        ++i;
    }
    int pointer = limit-count;
    for (i=0;           i < limit-count ; ++i) {
        if (out_live_array[i]==0) {pointer = i; break;}
    }
    for (i=pointer;     i < limit-count ; ++i) {
        if (out_live_array[i]!=0) {
            out_live_array[pointer] = out_live_array[i];
            ++pointer;
        }
    }
    for (i=limit-count; i < limit       ; ++i) {
        out_live_array[i] = 0;
    }
    *out_block_bound = limit-count;
    return;
};

static void readfn (Fn *fn) {

  Tmp * vars_array = fn->tmp;
  int vars_array_size = fn->ntmp;
  /** Набор базовых блоков, с границей (числом Out пременных) каждый**/
  Blk* base_blocks[L_MAX];
  int   out_block_bound[L_MAX];
  int   block_counter = 0;
  /** Для каждого ББ определено множество In, def, Out (что есть незаконченная live)**/
  char** in_array[L_MAX];
  char** out_live_array[L_MAX];
  char** def_block_array[L_MAX];

  for (Blk *blk = fn->start; blk; blk = blk->link) {
    /** Выделение памяти под временные наборы переменных**/
    char** def_array = (char**) malloc ((L_MAX+1)*sizeof(char*));
    int def_bound = 0;
    char** use_array = (char**) malloc ((L_MAX+1)*sizeof(char*));
    int use_bound = 0;

    {
        def_array[0] = 0;
        use_array[0] = 0;
        if ((def_array==0) || (use_array==0)) return;
    }

    Ins *ins = blk->ins;

    for (int n=0; n < blk->nins; ++n) {
            Ref *out = &(ins[n].to);
            Ref *in0 = &(ins[n].arg[0]);
            Ref *in1 = &(ins[n].arg[1]);
            if (is_named_var(in0)){
                char * name = vars_array[in0->val].name;
                if (strlen(name)!=0) {
                    if (! check_in(def_array, name) && ! check_in(use_array, name)){
                        add_elem(use_array, &use_bound, name);
                    }
                }
            }
            if (is_named_var(in1)){
                char * name = vars_array[in1->val].name;
                if (strlen(name)!=0) {
                    if (! check_in(def_array, name) && ! check_in(use_array, name)){
                        add_elem(use_array, &use_bound, name);
                    }
                }
            }
            if (is_named_var(out)){
                char * name = vars_array[out->val].name;
                if (strlen(name)!=0) {
                    if (! check_in(def_array, name)){
                        add_elem(def_array, &def_bound, name);
                    }
                }
            }
        }
        if (is_final_BLK(blk)) {
                Ref *jmp = &(blk->jmp.arg);
                char * name = vars_array[jmp -> val].name;
                if (strlen(name)!=0) {
                    if (! check_in(def_array, name) && ! check_in(use_array, name)){
                        add_elem(use_array, &use_bound, name);
                    }
                }
        }

        {   /** запись всех полученных значений в глобальные поля **/
            base_blocks     [block_counter] = blk;
            def_block_array [block_counter] = def_array;
            out_live_array  [block_counter] = (char **) malloc((L_MAX+1)*sizeof(char*));
            out_block_bound [block_counter] = 0;
            in_array        [block_counter] = use_array;
            if (block_counter==L_MAX) return;
            ++block_counter;
        }
    }
    /*
    for (int i=0; i<block_counter; ++i){
        int n;
        printf("\n\tdef = ");
        n=0;
        while (def_block_array[i][n]!=0) {
            printf("%%%s ", def_block_array[i][n]);
            ++n;
        }
        printf("\n\tuse = ");
        n=0;
        while (in_array[i][n]!=0) {
            printf("%%%s ", in_array[i][n]);
            ++n;
        }
        printf("\n\n");
    }*/
    {
        int Flag = 1;
        while (Flag) {
            /** до тех пор, пока не прекратятся изменения **/
            Flag = 0;
            /** проход по всем блокам в физическом порядке **/
            for (int num=0; num < block_counter ; ++num) {
                /* для заданного ББ NUM */
                int dummy = out_block_bound[num];
                Blk *current_block = base_blocks[num];
                Blk *check_block;
                int check_pos;
                /* для первого потомка S1 (преемника, элемента succ) */
                check_block=current_block->s1;
                if (check_block!=0) {
                    /* временный массив temp */
                    char *temp_array [L_MAX+1];
                    temp_array[0]=0;
                    int temp_int = 0;
                    /* позиция потомка S*/
                    check_pos = find_pos(base_blocks, check_block);
                    /* temp V= Out[S] */
                    array_union(temp_array, &temp_int, out_live_array[check_pos]);
                    /* temp \= def[S] */
                    set_difference(temp_array, &temp_int, def_block_array[check_pos]);
                    /* Out[NUM] V= temp*/
                    array_union(out_live_array[num], &(out_block_bound[num]), temp_array);
                    /* Out[NUM] V= In[S]*/
                    array_union(out_live_array[num], &(out_block_bound[num]), in_array[check_pos]);

                }
                /* для второго потомка (преемника, элемента succ) */
                /* Ровно такой же блок, никаких изменений. Много зависимостей, поэтому не выношу в функцию. */
                check_block=current_block->s2;
                if (check_block!=0) {
                    char *temp_array [L_MAX+1];
                    temp_array[0]=0;
                    int temp_int = 0;
                    check_pos = find_pos(base_blocks, check_block);
                    array_union(temp_array, &temp_int, out_live_array[check_pos]);
                    set_difference(temp_array, &temp_int, def_block_array[check_pos]);
                    array_union(out_live_array[num], &(out_block_bound[num]), temp_array);
                    array_union(out_live_array[num], &(out_block_bound[num]), in_array[check_pos]);

                }
                if (dummy!=out_block_bound[num]) Flag = 1;
            }
        }
    }
    {
        /** вывод на печать в заданном формате **/
        for (int i=0; i<block_counter; ++i){
            printf("@%s", base_blocks[i]->name);
            printf("\n\tlv_out = ");
            print_blk_set(out_live_array[i]);
            printf("\n\n");
        }
    }
    {
        /** чистка **/
        for (int num=0; num < block_counter ; ++num) {
            free (def_block_array   [num]);
            free (out_live_array    [num]);
            free (in_array          [num]);
        }
    }
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}
