#include <boost/thread.hpp>
#include <cstdio>
#include <boost/bind.hpp>

#include <boost/interprocess/sync/interprocess_semaphore.hpp>

struct sems {

  sems(int k) : m(1), b(0),n(k),count(0) {}
  boost::interprocess::interprocess_semaphore 
     m,b;
  int n,count;
};
sems * s; 

boost::barrier *bar;

void f(int k)
{   
   printf("t%d: a\n",k);
   s->m.wait();
   s->count++;
   s->m.post();
   if(s->count == s->n) 
      s->b.post();
   s->b.wait();
   s->b.post();
   printf("t%d: b\n",k);

}

/*
 * wykrzystanie bariery wbudowanej w boost'a
boost::barrier *barr;  
void foo(int k)
{ 
   printf("t%d: a\n",k);  	 
   barr->wait();  	 
   printf("t%d: b\n",k); 
}
*/
int main(int arc,char **argv)
{
   int k = atoi(argv[1]);
   boost::thread_group tpool; 
   //barr = new boost::barrier(k);
   s = new sems(k);
   for(int i=0;i<k;i++)
   {
      tpool.create_thread(boost::bind(&f,i));
   }
   tpool.join_all();
   return 0;
}

