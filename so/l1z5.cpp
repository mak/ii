#include <boost/thread.hpp>
#include <cstdio>
#include <boost/bind.hpp>

#include <boost/interprocess/sync/interprocess_semaphore.hpp>
struct sems {

  sems(int k) : m(1), t1(0),t2(1),count(0),n(k) {}
  boost::interprocess::interprocess_semaphore 
     m,t1,t2;
  int count,n;
};
sems * s; 


void f(int k)
{   
   while(true){
   printf("t%d: a\n",k);
   
   s->m.wait();
    s->count++;
    if(s->count == s->n) 
    {
       s->t2.wait();
       s->t1.post();
    }
   s->m.post();
   
   s->t1.wait();
   s->t1.post();
   
   printf("t%d: b\n",k);

   s->m.wait();
    s->count--;
    if(s->count == 0) 
    {
       s->t1.wait();
       s->t2.post();
    }
   s->m.post();
   
   s->t2.wait();
   s->t2.post();
   }

}
int main(int arc,char **argv)
{
   int k = atoi(argv[1]);
   boost::thread_group tpool; 
   s = new sems(k);
   for(int i=0;i<k;i++)
   {
      tpool.create_thread(boost::bind(&f,i));
   }
   tpool.join_all();
   return 0;
}

