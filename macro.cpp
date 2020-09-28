 enum J {
     Jxxx,
 #define JMPS(X)                                 \
     X(ret0)   X(retw)   X(retl)   X(rets)   \
     X(retd)   X(retc)   X(jmp)    X(jnz)    \
     X(jfieq)  X(jfine)  X(jfisge) X(jfisgt) \
     X(jfisle) X(jfislt) X(jfiuge) X(jfiugt) \
     X(jfiule) X(jfiult) X(jffeq)  X(jffge)  \
     X(jffgt)  X(jffle)  X(jfflt)  X(jffne)  \
     X(jffo)   X(jffuo)
 #define X(j) J##j,
     JMPS(X)                 
 #undef X
     NJmp
 };

static char *jtoa[NJmp] = {
#define X(j) [J##j] = #j,
         JMPS(X)
#undef X
  };