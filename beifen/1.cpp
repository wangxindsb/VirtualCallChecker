class A {
public:
  virtual void foo()=0;
  A() {foo();}
};

class B : public A {
public:
  B() {
  }
  ~B() {
   foobar();
  }
  virtual void foo();
  virtual void foobar();
};

int main() {
  B b;
}
