#ifndef _interface_h_
#define _interface_h_ 1

typedef enum {
  GOPERATOR_OEQUAL,
  GOPERATOR_ODIFF,
  GOPERATOR_OLESS
} goperator_t;

#ifndef _interface_cpp_
typedef struct HaskellModel_ HaskellModel;

HaskellModel *gecode_model_create(void);
HaskellModel *gecode_model_copy(HaskellModel *model);
HaskellModel *gecode_model_copy_reentrant(HaskellModel *model);
void gecode_model_destroy(HaskellModel *model);
int gecode_int_newvar(HaskellModel *model);
int gecode_int_rel(HaskellModel *model, int v1, goperator_t op, int v2);
int gecode_int_value(HaskellModel *model, int v, int val);
int gecode_int_mult(HaskellModel *model, int v1, int v2, int vr);
int gecode_int_div(HaskellModel *model, int v1, int v2, int vr);
int gecode_int_mod(HaskellModel *model, int v1, int v2, int vr);
int gecode_int_abs(HaskellModel *model, int v, int vr);
int gecode_int_dom(HaskellModel *model, int v, int low, int high);
int gecode_int_linear(HaskellModel *model, int num, int *vars, int *coef, goperator_t op, int val);
int gecode_int_alldiif(HaskellModel *model, int num, int *vars);
int gecode_int_sorted(HaskellModel *model, int num, int *vars, int strict);
void gecode_int_info(HaskellModel *model, int var, int *min, int *max, int *med, int *size, int *val);
int gecode_bool_newvar(HaskellModel *model);
#endif

#endif
