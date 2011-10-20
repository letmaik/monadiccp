#define _interface_cpp_

#include <vector>
#include <iostream>

#include "gecode/kernel.hh" 
#include "gecode/support.hh" 
#include "gecode/int.hh" 
#include "gecode/search.hh" 

#include "gecodeglue.h"

using namespace std;
using namespace Gecode;

int static nModels=0;
int static nOrigModels=0;

class HaskellModel : public Space {
protected:
  vector<BoolVar> boolVars;
  vector<IntVar> intVars;
  IntConLevel icl;
#ifndef NDEBUG
  int level;
  int origNum,num;
#endif
private:
  static IntRelType mapGoperator(goperator_t op, bool revert=false) {
    switch(op) {
      case GOPERATOR_OEQUAL: return IRT_EQ;
      case GOPERATOR_ODIFF: return IRT_NQ;
      case GOPERATOR_OLESS: return revert ? IRT_GR : IRT_LE;
    }
#ifndef NDEBUG
    cerr << "(unknown goperator " << op << "\n";
#endif
    assert(0);
  }
  
public:
  HaskellModel() : boolVars(), intVars(), icl(ICL_DEF)
#ifndef NDEBUG
  , level(0), origNum(++nOrigModels), num(++nModels) 
#endif
  {
#ifndef NDEBUG
    identify(); cerr << "newmodel\n";
#endif
  }
  ~HaskellModel() {
#ifndef NDEBUG
    identify(); cerr << "delmodel\n";
#endif
  }
  HaskellModel(bool share, HaskellModel &model) : Space(share,model), boolVars(model.boolVars.size()), intVars(model.intVars.size()), icl(model.icl)
#ifndef NDEBUG
  , level(model.level+1), origNum(model.origNum), num(++nModels)
#endif
   {
#ifndef NDEBUG
    identify(); cerr << "newmodel from [" << model.origNum << ":" << model.num << "]\n";
#endif
    for (int i=0; i<model.boolVars.size(); i++) {
      boolVars.at(i).update(*this, share, model.boolVars.at(i));
    }
    for (int i=0; i<model.intVars.size(); i++) {
      intVars.at(i).update(*this, share, model.intVars.at(i));
    }
  }
  virtual Space *copy(bool share) {
    return new HaskellModel(share, *this);
  }

#ifndef NDEBUG
  void identify() {
    for (int i=0; i<level; i++) {
      cerr << "  ";
    }
    cerr << "[" << origNum << ":" << num << "] ";
  }
#endif
  
  int addIntVar(int low, int high) {
    int ret = intVars.size();
    IntVar b(*this,low,high);
    intVars.push_back(b);
#ifndef NDEBUG
    identify(); cerr << "addintvar v" << ret << "\n";
#endif
    return ret;
  }
  int addBoolVar(int low, int high) {
    int ret = boolVars.size();
    BoolVar b(*this,low,high);
    boolVars.push_back(b);
#ifndef NDEBUG
    identify(); cerr << "addboolvar v" << ret << "\n";
#endif
    return ret;
  }
  void getIntInfo(int var, int *min, int *max, int *med, int *size, int *val) {
    assert(var>=0 && var<intVars.size());
    IntVar &v = intVars.at(var);
    SpaceStatus state=status();
    if (state==SS_FAILED) {
      if (min) *min=0;
      if (max) *max=0;
      if (med) *med=0;
      if (size) *size=0;
#ifndef NDEBUG
      identify(); cerr << "getintinfo failed)\n";
#endif
      return;
    }
    if (min) *min=v.min();
    if (max) *max=v.max();
    if (med) *med=v.med();
    int ss=v.size();
    if (ss==1) {
      if (size) *size=1;
      if (val) *val=v.val();
    } else {
      if (size) *size=ss;
    }
#ifndef NDEBUG
    identify(); cerr << "getintinfo v" << var << ": min=" << v.min() << ", max=" << v.max() << ", med=" << v.med() << ", size=" << v.size() << ", val=" << ((v.size()<2) ? v.val() : -666) << "\n";
#endif
  }
  int testIntDomain(int var, int val) {
    assert(var>=0 && var<intVars.size());
    return intVars.at(var).in(val);
  }
  void getBoolInfo(int var, int *bound, int *val) {
    assert(var>=0 && var<boolVars.size());
    BoolVar &v = boolVars.at(var);
    if (v.assigned()) {
      if (bound) *bound=1;
      if (val) *val=v.val();
    } else {
      if (bound) *bound=0;
    }
  }

  void postIntValue(int var, int val) {
    assert(var>=0 && var<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intvalue v" << var << " = " << val << "\n";
#endif
    IntVar &v = intVars.at(var);
    rel(*this,v,IRT_EQ,val,icl);
  }

  void postIntSame(int var1, int var2) {
    assert(var1>=0 && var1<intVars.size());
    assert(var2>=0 && var2<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intsame v" << var1 << " = v" << var2 << "\n";
#endif
    IntVar &v1 = intVars.at(var1);
    IntVar &v2 = intVars.at(var2);
    rel(*this,v1,IRT_EQ,v2,icl);
  }

  void postIntDiff(int var1, int var2) {
    assert(var1>=0 && var1<intVars.size());
    assert(var2>=0 && var2<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intdiff v" << var1 << " != v" << var2 << "\n";
#endif
    IntVar &v1 = intVars.at(var1);
    IntVar &v2 = intVars.at(var2);
    rel(*this,v1,IRT_NQ,v2,icl);
  }
  
  void postIntRel(int var1, goperator_t op, int var2) {
    assert(var1>=0 && var1<intVars.size());
    assert(var2>=0 && var2<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intrel v" << var1 << " " << (op==GOPERATOR_OEQUAL ? "==" : (op==GOPERATOR_OLESS ? "<" : "!=")) << " v" << var2 << "\n";
#endif
    IntVar &v1 = intVars.at(var1);
    IntVar &v2 = intVars.at(var2);
    rel(*this,v1,mapGoperator(op),v2,icl);
  }
  
  void postIntRelCf(int v1, goperator_t op, int var2) {
    assert(var2>=0 && var2<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intrelcf " << v1 << " " << (op==GOPERATOR_OEQUAL ? "==" : (op==GOPERATOR_OLESS ? "<" : "!=")) << " v" << var2 << "\n";
#endif
    IntVar &v2 = intVars.at(var2);
    rel(*this,v2,mapGoperator(op,true),v1,icl);
  }

  void postIntRelCs(int var1, goperator_t op, int v2) {
    assert(var1>=0 && var1<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intrelcs v" << var1 << " " << (op==GOPERATOR_OEQUAL ? "==" : (op==GOPERATOR_OLESS ? "<" : "!=")) << " " << v2 << "\n";
#endif
    IntVar &v1 = intVars.at(var1);
    rel(*this,v1,mapGoperator(op),v2,icl);
  }

  void postIntMult(int var1, int var2, int varr) {
    assert(var1>=0 && var1<intVars.size());
    assert(var2>=0 && var2<intVars.size());
    assert(varr>=0 && varr<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intmult v" << var1 << " * v" << var2 << " = v" << varr << "\n";
#endif
    IntVar &v1 = intVars.at(var1);
    IntVar &v2 = intVars.at(var2);
    IntVar &vr = intVars.at(varr);
    mult(*this,v1,v2,vr,icl);
  }

  void postIntDiv(int var1, int var2, int varr) {
    assert(var1>=0 && var1<intVars.size());
    assert(var2>=0 && var2<intVars.size());
    assert(varr>=0 && varr<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intdiv v" << var1 << " / v" << var2 << " = v" << varr << "\n";
#endif
    IntVar &v1 = intVars.at(var1);
    IntVar &v2 = intVars.at(var2);
    IntVar &vr = intVars.at(varr);
    div(*this,v1,v2,vr,icl);
  }

  void postIntMod(int var1, int var2, int varr) {
    assert(var1>=0 && var1<intVars.size());
    assert(var2>=0 && var2<intVars.size());
    assert(varr>=0 && varr<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intmod v" << var1 << " mod v" << var2 << " = v" << varr << "\n";
#endif
    IntVar &v1 = intVars.at(var1);
    IntVar &v2 = intVars.at(var2);
    IntVar &vr = intVars.at(varr);
    mod(*this,v1,v2,vr,icl);
  }

  void postIntAbs(int var, int varr) {
    assert(var>=0 && var<intVars.size());
    assert(varr>=0 && varr<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intabs abs(v" << var << ") = v" << varr << "\n";
#endif
    IntVar &v = intVars.at(var);
    IntVar &vr = intVars.at(varr);
    abs(*this,v,vr,icl);
  }

  void postIntDom(int var, int low, int high) {
    assert(var>=0 && var<intVars.size());
#ifndef NDEBUG
    identify(); cerr << "intdom v" << var << " = [" << low << "," << high << "]\n";
#endif
    IntVar &v = intVars.at(var);
    dom(*this,v,low,high,icl);
  }

  void postIntLinear(int num, int *vars, int *coef, goperator_t op, int val) {
    IntVarArgs vrs(num);
    IntArgs vls(num,coef);
    for (int i=0; i<num; i++) {
      int id=vars[i];
      assert(id>=0 && id<intVars.size());
      vrs[i]=intVars.at(id);
    }
#ifndef NDEBUG
    identify(); cerr << "intlinear num=" << num << "\n";
#endif
    linear(*this,vls,vrs,mapGoperator(op),val,icl);
  }

  void postIntAlldiff(int num, int *vars) {
    IntVarArgs vrs(num);
    for (int i=0; i<num; i++) {
      int id=vars[i];
      assert(id>=0 && id<intVars.size());
      vrs[i]=intVars.at(id);
    }
#ifndef NDEBUG
    identify(); cerr << "intalldiff num=" << num << "\n";
#endif
    distinct(*this,vrs,icl);
  }

  void postIntSorted(int num, int *vars, int strict) {
    IntVarArgs vrs(num);
    for (int i=0; i<num; i++) {
      int id=vars[i];
      assert(id>=0 && id<intVars.size());
      vrs[i]=intVars.at(id);
    }
#ifndef NDEBUG
    identify(); cerr << "intsorted num=" << num << "\n";
#endif
    rel(*this,vrs,strict ? IRT_LE : IRT_LQ,icl);
  }

  void postIntBranching(int num, int *vars) {
    IntVarArgs vrs(num);
    for (int i=0; i<num; i++) {
      int id=vars[i];
      assert(id>=0 && id<intVars.size());
      vrs[i]=intVars.at(id);
    }
#ifndef NDEBUG
    identify(); cerr << "intbranch num=" << num << "\n";
#endif
    branch(*this,vrs, INT_VAR_SIZE_MIN, INT_VAL_SPLIT_MIN);
  }

  void postBoolBranching(int num, int *vars) {
    IntVarArgs vrs(num);
    for (int i=0; i<num; i++) {
      int id=vars[i];
      assert(id>=0 && id<intVars.size());
      vrs[i]=intVars.at(id);
    }
#ifndef NDEBUG
    identify(); cerr << "boolbranch num=" << num << "\n";
#endif
    branch(*this,vrs, INT_VAR_SIZE_MIN, INT_VAL_SPLIT_MIN);
  }


};

extern "C" HaskellModel *gecode_model_create(void) { return new HaskellModel(); }
extern "C" HaskellModel *gecode_model_copy(HaskellModel *model) { return (HaskellModel*)(model->clone(true)); }
extern "C" HaskellModel *gecode_model_copy_reentrant(HaskellModel *model) { return (HaskellModel*)(model->clone(false)); }
extern "C" void gecode_model_fail(HaskellModel *model) { model->fail(); }
extern "C" void gecode_model_destroy(HaskellModel *model) { delete model; }
extern "C" int gecode_int_rel(HaskellModel *model, int v1, goperator_t op, int v2) { model->postIntRel(v1,op,v2); return !model->failed(); }
extern "C" int gecode_int_rel_cf(HaskellModel *model, int v1, goperator_t op, int v2) { model->postIntRelCf(v1,op,v2); return !model->failed(); }
extern "C" int gecode_int_rel_cs(HaskellModel *model, int v1, goperator_t op, int v2) { model->postIntRelCs(v1,op,v2); return !model->failed(); }
extern "C" int gecode_int_newvar(HaskellModel *model) { return model->addIntVar(-1000000000,1000000000); }
extern "C" int gecode_int_value(HaskellModel *model, int v, int val) { model->postIntValue(v,val); return !model->failed(); }
extern "C" int gecode_int_mult(HaskellModel *model, int v1, int v2, int vr) { model->postIntMult(v1,v2,vr); return !model->failed(); }
extern "C" int gecode_int_div(HaskellModel *model, int v1, int v2, int vr) { model->postIntDiv(v1,v2,vr); return !model->failed(); }
extern "C" int gecode_int_mod(HaskellModel *model, int v1, int v2, int vr) { model->postIntMod(v1,v2,vr); return !model->failed(); }
extern "C" int gecode_int_abs(HaskellModel *model, int v, int vr) { model->postIntAbs(v,vr); return !model->failed(); }
extern "C" int gecode_int_dom(HaskellModel *model, int v, int low, int high) { model->postIntDom(v,low,high); return !model->failed(); }
extern "C" int gecode_int_linear(HaskellModel *model, int num, int *vars, int *coef, goperator_t op, int val) { model->postIntLinear(num,vars,coef,op,val); return !model->failed(); }
extern "C" int gecode_int_alldiff(HaskellModel *model, int num, int *vars) { model->postIntAlldiff(num,vars); return !model->failed(); }
extern "C" int gecode_int_sorted(HaskellModel *model, int num, int *vars, int strict) { model->postIntSorted(num,vars,strict); return !model->failed(); }
extern "C" void gecode_int_branch(HaskellModel *model, int num, int *vars) { model->postIntBranching(num,vars); }
extern "C" void gecode_int_info(HaskellModel *model, int var, int *min, int *max, int *med, int *size, int *val) { model->getIntInfo(var,min,max,med,size,val); }
extern "C" int gecode_bool_newvar(HaskellModel *model) { return model->addBoolVar(0,1); }
extern "C" void gecode_bool_branch(HaskellModel *model, int num, int *vars) { model->postBoolBranching(num,vars); }

extern "C" DFS<HaskellModel> *gecode_search_create(HaskellModel *model) { 
  DFS<HaskellModel> *srch=new DFS<HaskellModel>(model);
#ifndef NDEBUG
  model->identify(); cerr << "search " << srch << " created\n";
#endif
  return srch;
}

extern "C" void gecode_search_destroy(DFS<HaskellModel> *search) { 
#ifndef NDEBUG
  cerr << "[search " << search << "] destroyed\n";
#endif
  delete search;
}

extern "C" HaskellModel *gecode_search_next(DFS<HaskellModel> *search) { 
#ifndef NDEBUG
  cerr << "[search " << search << "] requesting next\n";
#endif
  HaskellModel *res=search->next();
#ifndef NDEBUG
  cerr << "[search " << search << "] requested next (" << res << ")\n";
#endif
  return res;
}
