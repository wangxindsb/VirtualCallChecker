class A {
};

class B {
public:
  B() {
    A a;
    foo();
  }
  virtual int foo();
};

int main(){
  B b;
}
