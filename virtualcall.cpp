class A {
public:
  A();
  A(int i);

  ~A() {};
  
  virtual int foo(); // from Sema: expected-note {{'foo' declared here}}
  virtual void bar();
  void f() {
    foo();
        // expected-warning:Call to virtual function during construction will not dispatch to derived class
  }
};

class B : public A {
public:
  B() {
    foo();
        // expected-warning:Call to virtual function during construction will not dispatch to derived class
  }
  ~B();
  
  virtual int foo();
  virtual void bar() { foo(); }
      // expected-warning:Call to virtual function during destruction will not dispatch to derived class
};

A::A() {
  f();
}

A::A(int i) {
  foo(); // From Sema: expected-warning {{call to pure virtual member function 'foo' has undefined behavior}}
      // expected-warning:Call to virtual function during construction will not dispatch to derived class
}

B::~B() {
  this->B::foo(); // no-warning
  this->B::bar();
  this->foo();
      // expected-warning:Call to virtual function during destruction will not dispatch to derived class
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
      // expected-warning:Call to virtual function during construction will not dispatch to derived class
}

class D : public B {
public:
  D() {
    foo(); // no-warning
  }
  ~D() { bar(); }
  int foo() final;
  void bar() final { foo(); } // no-warning
};

class E final : public B {
public:
  E() {
    foo(); // no-warning
  }
  ~E() { bar(); }
  int foo() override;
};

// Regression test: don't crash when there's no direct callee.
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
  virtual void f();
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
      // expected-warning:Call to virtual function during construction will not dispatch to derived class
    H& h = *this;
    h.f();
      // expected-warning:Call to virtual function during construction will not dispatch to derived class
  }
};

class X {
public:
  X() {
    g();
  }
  X(int i) {
    if (i > 0) {
      X x(i-1);
      x.g();
      // no warning
    }
    g();
      // expected-warning:Call to virtual function during construction will not dispatch to derived class
  }
  virtual void g();
};

int main() {
  A *a = new A;
  A a1(1);
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
}

#include "virtualcall.h"

#define AS_SYSTEM
#include "virtualcall.h"
#undef AS_SYSTEM
