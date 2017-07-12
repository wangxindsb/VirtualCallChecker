// RUN: %clang_analyze_cc1 -analyzer-checker=optin.cplusplus.VirtualCall -analyzer-store region -verify -std=c++11 %s

// RUN: %clang_analyze_cc1 -analyzer-checker=optin.cplusplus.VirtualCall -analyzer-store region -analyzer-config optin.cplusplus.VirtualCall:PureOnly=true -DPUREONLY=1 -verify -std=c++11 %s

class A {
public:
  A();

  ~A() {};
  
  virtual int foo()=0;
  virtual void bar()=0;
  void f() {
    foo();
        // expected-warning:Call to virtual function during construction
  }
};

class B : public A {
public:
  B() {
    foo();
        // expected-warning:Call to virtual function during construction
  }
  ~B();
  
  virtual int foo();
  virtual void bar() { foo(); }
      // expected-warning:Call to virtual function during destruction
};

A::A() {
  f();
}

B::~B() {
  this->B::foo(); // no-warning
  this->B::bar();
  this->foo();
      // expected-warning:Call to virtual function during destruction
}

class C : public B {
public:
  C();
  ~C();
  
  virtual int foo();
  void f(int i);
};

C::C() {
  f(foo());
      // expected-warning:Call to virtual function during construction
}

class D : public B {
public:
  D() {
    foo(); // no-warning
  }
  ~D() { bar(); }
  int foo() final;
  void bar() final { foo(); } 
  // no-warning
};

class E final : public B {
public:
  E() {
    foo(); // no-warning
  }
  ~E() { bar(); }
  int foo() override;
};

class F {
public:
  F() {
    void (F::* ptr)() = &F::foo;
    (this->*ptr)();
  }
  void foo();
};

class G {
public:
  G() {}
  virtual void bar();
  void foo() {
    bar();
      // no warning
  }
};

class H{
public:
  H() : initState(0) { init(); }
  int initState;
  virtual void f() const;
  void init() {
    if (initState)
      f();
      // no warning
  }

  H(int i) {
    G g;
    g.foo();
    g.bar();
      // no warning
    f();
      // expected-warning:Call to virtual function during construction
    H& h = *this;
    h.f();
      // expected-warning:Call to virtual function during construction
  }
};

class X {
public:
  X() {
    g();
      // expected-warning:Call to virtual function during construction
  }
  X(int i) {
    if (i > 0) {
      X x(i-1);
      x.g();
      // no warning
    }
    g();
      // expected-warning:Call to virtual function during construction
  }
  virtual void g();
};

class M;
class N {
public:
   virtual void virtualMethod();
   void callFooOfM(M*);
};
class M {
public:
  M() {
    N n;
    n.virtualMethod(); 
    // no warning
    n.callFooOfM(this);
  }
  virtual void foo();
};
void N::callFooOfM(M* m) {
    m->foo(); 
    // expected-warning:Call to virtual function during construction
}

class Y {
public:
  virtual void foobar();
  Y() {
    F f1;
    foobar();
  }
};

int main() {
  B b;
  C c;
  D d;
  E e;
  F f;
  G g;
  H h;
  H h1(1);
  X x;
  X x1(1);
  M m;
  Y *y = new Y;
  delete y;
}
