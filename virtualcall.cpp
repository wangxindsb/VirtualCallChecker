class A {
public:
  A();
  A(int i);

  ~A() {};
  
  virtual int foo(); // from Sema: expected-note {{'foo' declared here}}
  virtual void bar();
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

A::A(int i) {
  foo(); // From Sema: expected-warning {{call to pure virtual member function 'foo' has undefined behavior}}
      // expected-warning:Call to virtual function during construction
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
  G(){foo();}
  virtual void bar();
  void foo() {
    F s;
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
