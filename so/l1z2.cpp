#include <boost/thread.hpp>
#include <cstdio>
#include <boost/interprocess/sync/interprocess_semaphore.hpp>

struct sems {

  sems() : m1(1), m2(0) {}
  boost::interprocess::interprocess_semaphore m1,m2;
};

sems * s = new sems;

void f1(void)
{   
   puts("najpierw ja");
   s->m1.post();
   s->m2.wait();
   puts("znowu ja");

}

void f2(void)
{
   puts("potem ja");
   s->m2.post();
   s->m1.wait();
   puts("ja koncze");

}

int main(void)
{
   boost::thread t1(&f1);
   boost::thread t2(&f2);
   t2.join();
   t1.join();
   return 0;
}
