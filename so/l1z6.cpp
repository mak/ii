#include <boost/thread.hpp>
#include <cstdio>
#include <cstdlib>
#include <boost/interprocess/sync/interprocess_semaphore.hpp>
#include <boost/bind.hpp>

typedef boost::interprocess::interprocess_semaphore sem;

enum gender {MEN, WOMEN};

struct quee {
  quee(): m(0),k(0),mk(1),mm(1) {}

  int m,k;
  sem  mk,mm;
};
quee  *q;

void f(gender g)
{
   if(g == MEN)
   {
      q->mk.wait();
      if(q->k > 0) 
	 q->k--;
      else
      {
	 q->mm.wait();
	 q->m++;
	 printf("women: %d\t men: %d\n",q->k,q->m);
	 q->mm.post();
      }
      q->mk.post();
   }
   else 
   {      
      q->mm.wait();
      if(q->m > 0) 
	 q->m--;
      else
      {
	 q->mk.wait();
	 q->k++;
	 printf("women: %d\t men: %d\n",q->k,q->m);
	 q->mk.post();
      }
      q->mm.post();

   }
}

int main(int argc, char **argv)
{
   int t = atoi(argv[1]);
   q = new quee;
   gender a[2] = {MEN,WOMEN};
   srand(time(NULL));
   while(t!=0)
   {
      int x = rand() % 2;
      printf("Gender: %s\n",!x?"MEN":"WOMEN");
      boost::thread th(boost::bind(&f,a[x]));
      t--;
      th.join();
   }
   return 0;
	    

}
