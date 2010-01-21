#include <boost/thread.hpp>
#include <cstdio>
#include <cstdlib>
#include <boost/interprocess/sync/interprocess_semaphore.hpp>
#include <boost/bind.hpp>
#include <vector>
#include <list>

typedef boost::interprocess::interprocess_semaphore sem;

class Fifo 
{
   private:      
      
      std::list<sem*> *tquee;
      sem mutex;

   public:

      Fifo() : mutex(1)
      {
	 tquee = new std::list<sem*>;
      }

      ~Fifo()
      {
	 delete tquee;
      }

      void wait()
      {
	 sem *s;
	 s = new sem(0);	 
	 mutex.wait();
	 tquee->push_back(s);
	 mutex.post();
	 (tquee->back())->wait();
      }

      void signal()
      {
	 mutex.wait();
	 sem *s = tquee->front();
	 tquee->pop_front();
	 mutex.post();
	 s->post();
	 s->post();
      }
};

Fifo * f = new Fifo;

void foo(int k)
{
   f->wait();
   printf("t%d: a\n",k);

}

void bar(int k)
{
   printf("t%d: b\n",k);      
   f->signal();
}


int main(int arc,char **argv)
{
   int k = atoi(argv[1]);
   boost::thread_group tpool; 
   boost::thread_group tpool1;    
   for(int i=0;i<k;i++)
   {
      tpool.create_thread(boost::bind(&foo,i));
      tpool1.create_thread(boost::bind(&bar,i));
   }
   tpool.join_all();   
   tpool1.join_all();

   return 0;
}

