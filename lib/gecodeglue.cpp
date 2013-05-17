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

#ifndef NDEBUG
int static nModels=0;
int static nOrigModels=0;
#endif

class HaskellModel : public Space {
protected:
  vector<BoolVar> boolVars;
  vector<IntVar> intVars;
  vector<IntVarArgs> colVars;
  IntConLevel icl;
  int refcount;
  int minimizeVar;
#ifndef NDEBUG
  int level;
  int origNum,num;
#endif
  //void *dummy;
private:
  static IntRelType mapGoperator(goperator_t op, bool revert=false) {
    switch(op) {
      case GOPERATOR_OEQUAL: return IRT_EQ;
      case GOPERATOR_ODIFF: return IRT_NQ;
      case GOPERATOR_OLESS: return revert ? IRT_GR : IRT_LE;
      case GOPERATOR_OLESSEQUAL: return revert ? IRT_GQ : IRT_LQ;
    }
#ifndef NDEBUG
    cerr << "(unknown goperator " << op << "\n";
#endif
    assert(0);
    return((IntRelType)(-1));
  }

  BoolVar inline getBoolVar(int var) const {
#ifndef NDEBUG
    cerr << "getBoolVar(" << var << ")" << endl;
#endif
    assert(var>=0 && var<(int)boolVars.size());
    return (boolVars[var]);
  }
  IntVarArgs inline getColVar(int var) const {
#ifndef NDEBUG
    cerr << "getColVar(" << var << ")" << endl;
#endif
    assert(var>=0 && var<(int)colVars.size());
    return (colVars[var]);
  }
  IntVar inline getIntVar(int var) const {
#ifndef NDEBUG
    cerr << "getIntVar(" << var << ")" << endl;
#endif
    assert(var>=0);
    if (var & ~0xFFFF) {
      IntVarArgs col=getColVar((var >> 16)-1);
      var &= 0xFFFF;
      assert(((int)var)<(int)col.size());
      return (col[var]);
    }
    assert(var<(int)intVars.size());
    return (intVars[var]);
  }
  
  IntVar inline cost(void) const {
    return getIntVar(minimizeVar);
  }

public:
  HaskellModel() : boolVars(), intVars(), colVars(), icl(ICL_DEF), refcount(0), minimizeVar(-1)
#ifndef NDEBUG
  , level(0), origNum(++nOrigModels), num(++nModels) 
#endif
  {
    //dummy=malloc(8192);
#ifndef NDEBUG
    identify(); cerr << "newmodel\n";
#endif
  }
  ~HaskellModel() {
#ifndef NDEBUG
    identify(); cerr << "delmodel\n";
#endif
  }
  HaskellModel(bool share, HaskellModel &model) : Space(share,model), boolVars(model.boolVars.size()), intVars(model.intVars.size()), icl(model.icl), refcount(0), minimizeVar(model.minimizeVar)
#ifndef NDEBUG
  , level(model.level+1), origNum(model.origNum), num(++nModels)
#endif
   {
    //dummy=malloc(8192);
#ifndef NDEBUG
    identify(); cerr << "newmodel from [" << model.origNum << ":" << model.num << "]\n";
#endif
    for (int i=0; i<(int)model.boolVars.size(); i++) {
      boolVars.at(i).update(*this, share, model.boolVars.at(i));
    }
    for (int i=0; i<(int)model.intVars.size(); i++) {
      intVars.at(i).update(*this, share, model.intVars.at(i));
    }
    for (int i=0; i<(int)model.colVars.size(); i++) {
      IntVarArgs &col=model.colVars.at(i);
      IntVarArgs ncol=IntVarArgs(col.size());
      for (int j=0; j<(int)(col.size()); j++) {
        ncol[j].update(*this,share,col[j]);
      }
      colVars.push_back(ncol);
    }
  }
  virtual Space *copy(bool share) {
#ifndef NDEBUG
    identify(); cerr << "making copy\n";
#endif
    return new HaskellModel(share, *this);
  }

#ifndef NDEBUG
  void identify() const {
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
  int addColVarSize(int count, int low, int high) {
    int ret = colVars.size();
#ifndef NDEBUG
    identify(); cerr << "addcolvar v" << ret << " (size " << count << ", ["<<low<<".."<<high<<"])\n";
#endif
    IntVarArray b(*this,count,low,high);
    colVars.push_back(b);
    return ret;
  }
  int addColVarList(int count, int *iids) {
    int ret = colVars.size();
#ifndef NDEBUG
    identify(); cerr << "addcolvar v" << ret << " (list size " << count << ")\n";
#endif
    IntVarArgs b(count);
    for (int i=0; i<count; i++) {
      b[i]=getIntVar(iids[i]);
    }
    colVars.push_back(b);
    return ret;
  }
  int addColVarCat(int c1, int c2) {
    int ret = colVars.size();
#ifndef NDEBUG
    identify(); cerr << "addcolvar v" << ret << " (cat c" << c1 << " c"<< c2 <<")\n";
#endif
    int l1=colVars[c1].size();
    int l2=colVars[c2].size();
    IntVarArgs b(l1+l2);
    for (int i=0; i<l1; i++) {
      b[i]=colVars[c1][i];
    }
    for (int i=0; i<l2; i++) {
      b[i+l1]=colVars[c2][i];
    }
    colVars.push_back(b);
    return ret;
  }
  int addColVarTake(int c, int pos, int len) {
    int ret = colVars.size();
#ifndef NDEBUG
    identify(); cerr << "addcolvar v" << ret << " (take " << len << " from c" << c << " at "<< pos <<")\n";
#endif
    int count = len;
    if (colVars[c].size()-pos < count) count=colVars[c].size()-pos;
    if (count<0) count=0;
    IntVarArgs b(count);
    for (int i=0; i<count; i++) {
      b[i]=colVars[c][i+pos];
    }
    colVars.push_back(b);
    return ret;
  }

  void doPropagation(void) {
    status();
  }
  int getIntSize(int var) {
    IntVar v=getIntVar(var);
    SpaceStatus state=status();
    if (state==SS_FAILED) {
      return 0;
    }
    return v.size();
  }
  int getIntValue(int var) {
    IntVar v=getIntVar(var);
    return v.val();
  }
  int getIntMedian(int var) {
    return getIntVar(var).med();
  }
  void getIntInfo(int var, int *ptr) { 
    IntVar v=getIntVar(var);
    SpaceStatus state=status();
    if (state==SS_FAILED) {
      ptr[0]=0;
      ptr[1]=0;
      ptr[2]=0;
      ptr[3]=0;
#ifndef NDEBUG
      identify(); cerr << "getintinfo failed)\n";
#endif
      return;
    }
    ptr[0]=v.min();
    ptr[1]=v.max();
    ptr[2]=v.med();
    int ss=v.size();
    if (ss==1) {
      ptr[3]=1;
      ptr[4]=v.val();
    } else {
      ptr[3]=ss;
    }
#ifndef NDEBUG
    identify(); cerr << "getintinfo v" << var << ": min=" << v.min() << ", max=" << v.max() << ", med=" << v.med() << ", size=" << v.size() << ", val=" << ((v.size()<2) ? v.val() : -666) << "\n";
#endif
  }
  int testIntDomain(int var, int val) {
    return getIntVar(var).in(val);
  }
  int getBoolInfo(int var) {
    SpaceStatus state=status();
    if (state==SS_FAILED) return -2;
    BoolVar v = getBoolVar(var);
    if (v.assigned()) {
      return (v.val() ? 1 : 0);
    } else {
      return -1;
    }
  }

  void postIntValue(int var, int val) {
    IntVar v=getIntVar(var);
#ifndef NDEBUG
    identify(); cerr << "intvalue v" << var << " = " << val << "\n";
#endif
    rel(*this,v,IRT_EQ,val,icl);
  }

  void postIntSame(int var1, int var2) {
    IntVar v1 = getIntVar(var1);
    IntVar v2 = getIntVar(var2);
#ifndef NDEBUG
    identify(); cerr << "intsame v" << var1 << " = v" << var2 << "\n";
#endif
    rel(*this,v1,IRT_EQ,v2,icl);
  }

  void postBoolSame(int var1, int var2) {
#ifndef NDEBUG
    identify(); cerr << "intsame v" << var1 << " = v" << var2 << "\n";
#endif
    rel(*this,getBoolVar(var1),IRT_EQ,getBoolVar(var2),icl);
  }

  void postIntDiff(int var1, int var2) {
    IntVar v1 = getIntVar(var1);
    IntVar v2 = getIntVar(var2);
#ifndef NDEBUG
    identify(); cerr << "intdiff v" << var1 << " != v" << var2 << "\n";
#endif
    rel(*this,v1,IRT_NQ,v2,icl);
  }
  
  void postIntRel(int var1, goperator_t op, int var2) {
    IntVar v1 = getIntVar(var1);
    IntVar v2 = getIntVar(var2);
#ifndef NDEBUG
    identify(); cerr << "intrel v" << var1 << " " << (op==GOPERATOR_OEQUAL ? "==" : (op==GOPERATOR_OLESS ? "<" : "!=")) << " v" << var2 << "\n";
#endif
    rel(*this,v1,mapGoperator(op),v2,icl);
  }
  
  void postIntRelCf(int v1, goperator_t op, int var2) {
    IntVar v2 = getIntVar(var2);
#ifndef NDEBUG
    identify(); cerr << "intrelcf " << v1 << " " << (op==GOPERATOR_OEQUAL ? "==" : (op==GOPERATOR_OLESS ? "<" : "!=")) << " v" << var2 << "\n";
#endif
    rel(*this,v2,mapGoperator(op,true),v1,icl);
  }

  void postIntRelCs(int var1, goperator_t op, int v2) {
    IntVar v1 = getIntVar(var1);
#ifndef NDEBUG
    identify(); cerr << "intrelcs v" << var1 << " " << (op==GOPERATOR_OEQUAL ? "==" : (op==GOPERATOR_OLESS ? "<" : "!=")) << " " << v2 << "\n";
#endif
    rel(*this,v1,mapGoperator(op),v2,icl);
  }

  void postIntMult(int var1, int var2, int varr) {
    IntVar v1 = getIntVar(var1);
    IntVar v2 = getIntVar(var2);
    IntVar vr = getIntVar(varr);
#ifndef NDEBUG
    identify(); cerr << "intmult v" << var1 << " * v" << var2 << " = v" << varr << "\n";
#endif
    mult(*this,v1,v2,vr,icl);
  }

  void postIntDiv(int var1, int var2, int varr) {
    IntVar v1 = getIntVar(var1);
    IntVar v2 = getIntVar(var2);
    IntVar vr = getIntVar(varr);
#ifndef NDEBUG
    identify(); cerr << "intdiv v" << var1 << " / v" << var2 << " = v" << varr << "\n";
#endif
    div(*this,v1,v2,vr,icl);
  }

  void postIntMod(int var1, int var2, int varr) {
    IntVar v1 = getIntVar(var1);
    IntVar v2 = getIntVar(var2);
    IntVar vr = getIntVar(varr);
#ifndef NDEBUG
    identify(); cerr << "intmod v" << var1 << " mod v" << var2 << " = v" << varr << "\n";
#endif
    mod(*this,v1,v2,vr,icl);
  }

  void postIntAbs(int var, int varr) {
    IntVar v =  getIntVar(var);
    IntVar vr = getIntVar(varr);
#ifndef NDEBUG
    identify(); cerr << "intabs abs(v" << var << ") = v" << varr << "\n";
#endif
    abs(*this,v,vr,icl);
  }

  void postIntDom(int var, int low, int high) {
    IntVar v = getIntVar(var);
#ifndef NDEBUG
    identify(); cerr << "intdom v" << var << " = [" << low << "," << high << "]\n";
#endif
    dom(*this,v,low,high,icl);
  }

  void postIntLinear(int num, int *vars, int *coef, goperator_t op, int val) {
    IntVarArgs vrs(num);
    IntArgs vls(num,coef);
    for (int i=0; i<num; i++) {
      vrs[i] = getIntVar(vars[i]);
    }
#ifndef NDEBUG
    IntArgs dbg(num,vars);
    identify(); cerr << "intlinear num=" << num << " vars=" << dbg << " coefs=" << vls << " op=" << (op==GOPERATOR_OEQUAL ? "==" : (op==GOPERATOR_OLESS ? "<" : (op==GOPERATOR_OLESSEQUAL ? "<=" : "!="))) << " cte=" << val << "\n";
#endif
    linear(*this,vls,vrs,mapGoperator(op),val,icl);
  }

  void postIntLinearReif(int num, int *vars, int *coef, goperator_t op, int val, int reif) {
    IntVarArgs vrs(num);
    IntArgs vls(num,coef);
    for (int i=0; i<num; i++) {
      vrs[i] = getIntVar(vars[i]);
    }
#ifndef NDEBUG
    identify(); cerr << "intlinear num=" << num << "\n";
#endif
    linear(*this,vls,vrs,mapGoperator(op),val,getBoolVar(reif),icl);
  }

  void postIntAlldiff(int num, int *vars,int dom) {
    IntVarArgs vrs(num);
    for (int i=0; i<num; i++) {
      vrs[i] = getIntVar(vars[i]);
    }
#ifndef NDEBUG
    identify(); cerr << "intalldiff num=" << num << "\n";
#endif
    distinct(*this,vrs,dom ? ICL_DOM : icl);
  }

  void postColAlldiff(int var, int dom) {
    IntVarArgs vars=getColVar(var);
#ifndef NDEBUG
    identify(); cerr << "colalldiff col=" << var << "\n";
#endif
    distinct(*this,vars,dom ? ICL_DOM : icl);
  }

  void postColSorted(int var, goperator_t op) {
    IntVarArgs vars=getColVar(var);
#ifndef NDEBUG
    identify(); cerr << "colsorted col=" << var << " op=" << op << "\n";
#endif
    rel(*this,vars,mapGoperator(op),icl);
  }

  void postColSum(int col,int var) {
    IntVarArgs vars=getColVar(col);
    IntVar sum=getIntVar(var);
#ifndef NDEBUG
    identify(); cerr << "colsum col=" << col << " sumvar=" << var << "\n";
#endif
    linear(*this,vars,IRT_EQ,sum,icl);
  }

  void postColSumC(int col,int val) {
    IntVarArgs vars=getColVar(col);
#ifndef NDEBUG
    identify(); cerr << "colsum col=" << col << " sumval=" << val << "\n";
#endif
    linear(*this,vars,IRT_EQ,val,icl);
  }

  void postIntSorted(int num, int *vars, goperator_t op) {
    IntVarArgs vrs(num);
    for (int i=0; i<num; i++) {
      vrs[i] = getIntVar(vars[i]);
    }
#ifndef NDEBUG
    identify(); cerr << "intsorted num=" << num << "\n";
#endif
    rel(*this,vrs,mapGoperator(op),icl);
  }

  void postIntBranching(int num, int *vars) {
    IntVarArgs vrs(num);
    for (int i=0; i<num; i++) {
      vrs[i] = getIntVar(vars[i]);
    }
#ifndef NDEBUG
    identify(); cerr << "intbranch num=" << num << "\n";
#endif
    branch(*this,vrs, INT_VAR_SIZE_MIN, INT_VAL_SPLIT_MIN);
  }

  void postBoolBranching(int num, int *vars) {
    BoolVarArgs vrs(num);
    for (int i=0; i<num; i++) {
      vrs[i] = getBoolVar(vars[i]);
    }
#ifndef NDEBUG
    identify(); cerr << "intbranch num=" << num << "\n";
#endif
    branch(*this,vrs, INT_VAR_SIZE_MIN, INT_VAL_SPLIT_MIN);
  }
  
  void postColCount(int col,int isValConst,int val,goperator_t op,int isCountConst,int count) {
    IntVarArgs vcol=getColVar(col);
#ifndef NDEBUG
    identify(); cerr << "count col=" << col << " val=" << (isValConst ? "#" : "v") << val << " rel=" << op << " count=" << (isCountConst ? "#" : "v") << count << "\n";
#endif
    switch ((isValConst!=0) | ((isCountConst!=0)*2)) {
      case 0: {
        IntVar vval=getIntVar(val);
        IntVar vcount=getIntVar(count);
        Gecode::count(*this,vcol,vval,mapGoperator(op),vcount);
        break;
      }
      case 1: {
        IntVar vcount=getIntVar(count);
        Gecode::count(*this,vcol,val,mapGoperator(op),vcount);
        break;
      }
      case 2: {
        IntVar vval=getIntVar(val);
        Gecode::count(*this,vcol,vval,mapGoperator(op),count);
        break;
      }
      case 3: {
        Gecode::count(*this,vcol,val,mapGoperator(op),count);
        break;
      }
    }
  }
  
  void postColBranching(int num, int *vars) {
    int n=0;
#ifndef NDEBUG
    identify(); cerr << "colbranch num=" << num << "\n";
#endif
    for (int i=0; i<num; i++) {
      n += getColVar(vars[i]).size();
    }
    IntVarArgs vrs(n);
    int p=0;
    for (int i=0; i<num; i++) {
      IntVarArgs col=(getColVar(vars[i]));
      int s=col.size();
      for (int k=0; k<s; k++) {
        vrs[p++]=col[k];
      }
    }
    branch(*this,vrs,INT_VAR_SIZE_MIN, INT_VAL_SPLIT_MIN);
  }

  void postBoolValue(int var, int val) {
#ifndef NDEBUG
    identify(); cerr << "boolval var="<<var<<" val="<<val<<"\n";
#endif
    rel(*this,getBoolVar(var),IRT_EQ,val,icl);
  }

  int postColEqual(int c1, int c2) {
    IntVarArgs col1= getColVar(c1);
    IntVarArgs col2= getColVar(c2);
#ifndef NDEBUG
    identify(); cerr << "colequal col1="<<c1<<" col="<<c2<<"\n";
#endif
    int len=col1.size();
    if (len != (int)(col2.size())) return 0;
    for (int i=0; i<len; i++) {
      rel(*this,col1[i],IRT_EQ,col2[i],icl);
    }
    return 1;
  }

  int postColCat(int c1, int c2, int cr) {
#ifndef NDEBUG
    identify(); cerr << "colcat col1="<<c1<<" col2="<<c2<<" colr="<<cr<<"\n";
#endif
    IntVarArgs col1= getColVar(c1);
    IntVarArgs col2= getColVar(c2);
    IntVarArgs colr= getColVar(cr);
    int len1=col1.size();
    int len2=col2.size();
    int lenr=colr.size();
    if (lenr != len1+len2) return 0;
    for (int i=0; i<len1; i++) {
      rel(*this,col1[i],IRT_EQ,colr[i],icl);
    }
    for (int i=0; i<len2; i++) {
      rel(*this,col2[i],IRT_EQ,colr[i+len1],icl);
    }
    return 1;
  }

  int postColTake(int c, int p, int l, int cr) {
#ifndef NDEBUG
    identify(); cerr << "coltake col=v"<<c<<" pos="<<p<<" len="<<l<<" colr="<<cr<<"\n";
#endif
    IntVarArgs col=  getColVar(c);
    IntVarArgs colr= getColVar(cr);
    int len=col.size();
    int lenr=colr.size();
    if (l+p>len) l=len-p;
    if (l>0) l=0;
    if (lenr != l) return 0;
    for (int i=0; i<l; i++) {
      rel(*this,col[i+p],IRT_EQ,colr[i],icl);
    }
    return 1;
  }

  void postColAt(int c, int p, int i) {
#ifndef NDEBUG
    identify(); cerr << "colat col=v"<<c<<" pos=v"<<p<<" res=v"<<i<<"\n";
#endif
    element(*this,getColVar(c),getIntVar(p),getIntVar(i),icl);
  }

  void postColAtList(int n, int *l, int p, int i) {
    IntArgs args(n,l);
#ifndef NDEBUG
    identify(); cerr << "colat col=[...] pos=v"<<p<<" res=v"<<i<<"\n";
#endif
    element(*this,args,getIntVar(p),getIntVar(i),icl);
  }

  void postColAtConst(int c, int p, int v) {
#ifndef NDEBUG
    identify(); cerr << "colat col=v"<<c<<" pos=v"<<p<<" res="<<v<<"\n";
#endif
    element(*this,getColVar(c),getIntVar(p),v,icl);
  }

  void postColAtListConst(int n, int *l, int p, int v) {
    IntArgs args(n,l);
#ifndef NDEBUG
    identify(); cerr << "colat col=[...] pos=v"<<p<<" res="<<v<<"\n";
#endif
    element(*this,args,getIntVar(p),v,icl);
  }

  void postDom(int i,int c) {
    IntVar iv = getIntVar(i);
    IntVarArgs iva = getColVar(c);
    count(*this,iva,iv,IRT_GR,0,icl);
  }

  void postDom(int i, int n, const int *c, int r) {
    IntVar iv = getIntVar(i);
    IntArgs ia(n,c);
    IntSet is(ia);
    if (r<0) {
      dom(*this,iv,is,icl);
    } else {
      BoolVar rv = getBoolVar(r);
      dom(*this,iv,is,rv,icl);
    }
  }

  void postBoolChannel(int b, int i) {
#ifndef NDEBUG
    identify(); cerr << "channel bool=v"<<b<<" int=v"<<i<<"\n";
#endif
    channel(*this,getBoolVar(b),getIntVar(i),icl);
  }

  void postBoolAnd(int a, int b, int r) {
#ifndef NDEBUG
    identify(); cerr << "and a=v"<<a<<" b=v"<<b<<" r=v"<<r<<"\n";
#endif
    rel(*this,getBoolVar(a),BOT_AND,getBoolVar(b),getBoolVar(r),icl);
  }

  void postBoolOr(int a, int b, int r) {
#ifndef NDEBUG
    identify(); cerr << "or a=v"<<a<<" b=v"<<b<<" r=v"<<r<<"\n";
#endif
    rel(*this,getBoolVar(a),BOT_OR,getBoolVar(b),getBoolVar(r),icl);
  }

  void postBoolEquiv(int a, int b, int r) {
#ifndef NDEBUG
    identify(); cerr << "boolequiv a=v"<<a<<" b=v"<<b<<" r=v"<<r<<"\n";
#endif
    rel(*this,getBoolVar(a),BOT_EQV,getBoolVar(b),getBoolVar(r),icl);
  }

  void postBoolNot(int a, int r) {
#ifndef NDEBUG
    identify(); cerr << "not a=v"<<a<<" r=v"<<r<<"\n";
#endif
    rel(*this,getBoolVar(a),IRT_NQ,getBoolVar(r),icl);
  }

  void postBoolAll(int num, int *vars, int r) {
#ifndef NDEBUG
    identify(); cerr << "boolall num="<<num<<" r=v"<<r<<"\n";
#endif
    BoolVarArgs vrs(num);
    for (int i=0; i<num; i++) {
      vrs[i] = getBoolVar(vars[i]);
    }
    if (r<0) {
      rel(*this,BOT_AND,vrs,true);
    } else {
      BoolVar reif=getBoolVar(r);
      rel(*this,BOT_AND,vrs,reif);
    }
  }

  void postBoolAny(int num, int *vars, int r) {
#ifndef NDEBUG
    identify(); cerr << "boolany num="<<num<<" r=v"<<r<<"\n";
#endif
    BoolVarArgs vrs(num);
    for (int i=0; i<num; i++) {
      vrs[i] = getBoolVar(vars[i]);
    }
    if (r<0) {
      rel(*this,BOT_OR,vrs,true);
    } else {
      BoolVar reif=getBoolVar(r);
      rel(*this,BOT_OR,vrs,reif);
    }
  }

  int getColSize(int var) const {
    IntVarArgs vr=getColVar(var);
#ifndef NDEBUG
    identify(); cerr << "get colsize: col=v"<<var<<": res="<<vr.size()<<"\n";
#endif
    return vr.size();
  }

  int modRefcount(int m) {
#ifndef NDEBUG
    identify(); cerr << "mod refcount: "<<refcount<<" -> "<<(refcount+m)<<"\n";
#endif
    refcount += m;
    return refcount;
  }

  void message(const string chr) const {
#ifndef NDEBUG
    identify(); cerr << chr << "\n";
#endif
  }

  void setMinimizeVar(int v) {
#ifndef NDEBUG
    identify(); cerr << "set minimizevar: v"<<v<<"\n";
#endif
    minimizeVar=v;
  }

  void constrain(const Space& _best) {
    const HaskellModel *best=(HaskellModel*)(&_best);
    rel(*this,cost(),IRT_LE,best->cost().val());
  }
};

extern "C" HaskellModel *gecode_model_create(void) { return new HaskellModel(); }
extern "C" HaskellModel *gecode_model_copy(HaskellModel *model) { 
  SpaceStatus state=model->status();
  if (state==SS_FAILED) {
    return NULL;
  } else {
    return (HaskellModel*)(model->clone(true));
  }
}
extern "C" HaskellModel *gecode_model_copy_reentrant(HaskellModel *model) {
  SpaceStatus state=model->status();
  if (state==SS_FAILED) {
    return NULL;
  } else {
    return (HaskellModel*)(model->clone(false));
  }
}
extern "C" void gecode_model_fail(HaskellModel *model) { model->message("fail"); model->fail(); }
extern "C" void gecode_model_destroy(HaskellModel *model) { model->message("destroy"); delete model; }
extern "C" void gecode_model_propagate(HaskellModel *model) { model->doPropagation(); }
extern "C" int gecode_int_rel(HaskellModel *model, int v1, goperator_t op, int v2) { model->postIntRel(v1,op,v2); return !model->failed(); }
extern "C" int gecode_bool_equal(HaskellModel *model, int v1, goperator_t op, int v2) { model->postBoolSame(v1,v2); return !model->failed(); }
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
extern "C" int gecode_int_linear_ri(HaskellModel *model, int num, int *vars, int *coef, goperator_t op, int val, int reif) { model->postIntLinearReif(num,vars,coef,op,val,reif); return !model->failed(); }
extern "C" int gecode_int_alldiff(HaskellModel *model, int num, int *vars, int dom) { model->postIntAlldiff(num,vars,dom); return !model->failed(); }
extern "C" int gecode_int_sorted(HaskellModel *model, int num, int *vars, goperator_t op) { model->postIntSorted(num,vars,op); return !model->failed(); }
extern "C" void gecode_int_branch(HaskellModel *model, int num, int *vars) { model->postIntBranching(num,vars); }
extern "C" void gecode_int_info(HaskellModel *model, int var, int *ptr) { model->getIntInfo(var,ptr); }
extern "C" int gecode_int_get_size(HaskellModel *model, int var) { return model->getIntSize(var); }
extern "C" int gecode_int_get_value(HaskellModel *model, int var) { return model->getIntValue(var); }
extern "C" int gecode_int_get_median(HaskellModel *model, int var) { return model->getIntMedian(var); }
extern "C" int gecode_bool_newvar(HaskellModel *model) { return model->addBoolVar(0,1); }
extern "C" int gecode_bool_info(HaskellModel *model, int v) { return model->getBoolInfo(v); }
extern "C" int gecode_col_newsize(HaskellModel *model, int size) { return model->addColVarSize(size,-1000000000,1000000000); }
extern "C" int gecode_col_newlist(HaskellModel *model, int size, int *vars) { return model->addColVarList(size,vars); }
extern "C" int gecode_col_newcat(HaskellModel *model, int c1, int c2) { return model->addColVarCat(c1,c2); }
extern "C" int gecode_col_newtake(HaskellModel *model, int c, int p, int l) { return model->addColVarTake(c,p,l); }
extern "C" int gecode_col_cat(HaskellModel *model, int c1, int c2, int cr) { return model->postColCat(c1,c2,cr) && !model->failed(); }
extern "C" int gecode_col_take(HaskellModel *model, int c, int p, int l, int cr) { return model->postColTake(c,p,l,cr) && !model->failed(); }
extern "C" int gecode_col_equal(HaskellModel *model, int c1, int c2) { return model->postColEqual(c1,c2) && !model->failed(); }
extern "C" int gecode_col_at(HaskellModel *model, int c, int p, int i) { model->postColAt(c,p,i); return !model->failed(); }
extern "C" int gecode_col_at_lst(HaskellModel *model, int n, int *l, int p, int i) { model->postColAtList(n,l,p,i); return !model->failed(); }
extern "C" int gecode_col_at_cv(HaskellModel *model, int c, int p, int v) { model->postColAtConst(c,p,v); return !model->failed(); }
extern "C" int gecode_col_at_lst_cv(HaskellModel *model, int n, int *l, int p, int v) { model->postColAtListConst(n,l,p,v); return !model->failed(); }
extern "C" int gecode_col_dom(HaskellModel *model, int i, int c) { model->postDom(i,c); return !model->failed(); }
extern "C" int gecode_int_dom_list(HaskellModel *model, int i, int n, const int *l, int r) { model->postDom(i,n,l,r); return !model->failed(); }
extern "C" int gecode_col_getsize(HaskellModel *model, int c) { return model->getColSize(c); }
extern "C" int gecode_col_sorted(HaskellModel *model, int c, goperator_t op) { model->postColSorted(c,op); return !model->failed(); }
extern "C" int gecode_col_sum(HaskellModel *model, int c, int i) { model->postColSum(c,i); return !model->failed(); }
extern "C" int gecode_col_sumc(HaskellModel *model, int c, int v) { model->postColSumC(c,v); return !model->failed(); }
extern "C" int gecode_col_alldiff(HaskellModel *model, int c, int dom) { model->postColAlldiff(c,dom); return !model->failed(); }
extern "C" int gecode_col_count(HaskellModel *model, int col, int numconst, int num, goperator_t op, int countconst, int count) { model->postColCount(col,numconst,num,op,countconst,count); return !model->failed(); }
extern "C" void gecode_col_branch(HaskellModel *model, int num, int *vars) { model->postColBranching(num,vars); }
extern "C" void gecode_bool_branch(HaskellModel *model, int num, int *vars) { model->postBoolBranching(num,vars); }
extern "C" int gecode_bool_value(HaskellModel *model, int v, int val) { model->postBoolValue(v,val); return !model->failed(); }
extern "C" int gecode_bool_channel(HaskellModel *model, int b, int i) { model->postBoolChannel(b,i); return !model->failed(); }
extern "C" int gecode_bool_and(HaskellModel *model, int a, int b, int r) { model->postBoolAnd(a,b,r); return !model->failed(); }
extern "C" int gecode_bool_or(HaskellModel *model, int a, int b, int r) { model->postBoolOr(a,b,r); return !model->failed(); }
extern "C" int gecode_bool_not(HaskellModel *model, int a, int r) { model->postBoolNot(a,r); return !model->failed(); }
extern "C" int gecode_bool_equiv(HaskellModel *model, int a, int b, int r) { model->postBoolEquiv(a,b,r); return !model->failed(); }
extern "C" int gecode_bool_all(HaskellModel *model, int num, int *vars, int reif) { model->postBoolAll(num,vars,reif); return !model->failed(); }
extern "C" int gecode_bool_any(HaskellModel *model, int num, int *vars, int reif) { model->postBoolAny(num,vars,reif); return !model->failed(); }

extern "C" int gecode_space_modrefcount(HaskellModel *model, int mod) { return model->modRefcount(mod); }
extern "C" void gecode_space_setcost(HaskellModel *model,int var) { model->setMinimizeVar(var); }

enum gecode_search_type {
  GECODE_SEARCH_TYPE_DFS,
  GECODE_SEARCH_TYPE_BAB
};

union gecode_search_data_specific_t {
  DFS<HaskellModel> *dfs;
  BAB<HaskellModel> *bab;
};

typedef struct {
  enum gecode_search_type typ;
  union gecode_search_data_specific_t dat;
} gecode_search_data_t;

gecode_search_data_t static *gecode_search_create(HaskellModel *model, gecode_search_type typ) {
  Search::Options o = Search::Options();
  o.c_d = 1;
  gecode_search_data_t *srch=new gecode_search_data_t;
#ifndef NDEBUG
  model->identify(); cerr << "create search (type "<<typ<<")\n";
#endif
  srch->typ=typ;
  switch (typ) {
    case GECODE_SEARCH_TYPE_DFS: { 
      srch->dat.dfs=new DFS<HaskellModel>(model,o);
      break;
    }
    case GECODE_SEARCH_TYPE_BAB: {
      srch->dat.bab=new BAB<HaskellModel>(model,o);
      break;
    }
  }
  return srch;
}

extern "C" gecode_search_data_t *gecode_search_create_dfs(HaskellModel *model) { return gecode_search_create(model, GECODE_SEARCH_TYPE_DFS); }
extern "C" gecode_search_data_t *gecode_search_create_bab(HaskellModel *model) { return gecode_search_create(model, GECODE_SEARCH_TYPE_BAB); }

extern "C" void gecode_search_destroy(gecode_search_data_t *srch) { 
#ifndef NDEBUG
  cerr << "[search " << srch << "] destroyed\n";
#endif
  switch (srch->typ) {
    case GECODE_SEARCH_TYPE_DFS: {
      delete srch->dat.dfs;
      srch->dat.dfs=NULL;
      break;
    }
    case GECODE_SEARCH_TYPE_BAB: {
      delete srch->dat.bab;
      srch->dat.bab=NULL;
      break;
    }
  }
  delete srch;
}

extern "C" HaskellModel *gecode_search_next(gecode_search_data_t *srch) { 
#ifndef NDEBUG
  cerr << "[search " << srch << "] requesting next\n";
#endif
  HaskellModel *res;
  switch (srch->typ) {
    case GECODE_SEARCH_TYPE_DFS: {
      res=srch->dat.dfs->next();
      break;
    }
    case GECODE_SEARCH_TYPE_BAB: {
      res=srch->dat.bab->next();
      break;
    }
    default:
    res=NULL;
  }
#ifndef NDEBUG
  cerr << "[search " << srch << "] requested next (" << res << ")\n";
#endif
  return res;
}
