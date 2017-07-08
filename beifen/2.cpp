struct A;
struct X {
   virtual void virtualMethod();
   void callFooOfA(A*);
};
struct A {
  A() {
    X x;
    x.virtualMethod(); // this virtual call is ok
    x.callFooOfA(this);
  }
  virtual void foo();
};
void X::callFooOfA(A* a) {
   a->foo(); // Would be good to warn here.
}
  struct B {
    A a;
  };
  int main() {
    B b;
  }
