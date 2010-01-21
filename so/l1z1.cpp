#include <boost/thread.hpp>
#include <cstdio>
#include <boost/interprocess/sync/interprocess_semaphore.hpp>

boost::interprocess::interprocess_semaphore m(0);

void f1(void)
{
   
   puts("najpierw ja");
   m.post();
}

void f2(void)
{
   m.wait();
   puts("potem ja");
}

int main(void)
{
   boost::thread t1(&f1);
   boost::thread t2(&f2);
   t2.join();
   t1.join();
   return 0;
}
