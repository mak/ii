#include <boost/thread.hpp>
#include <cstdio>
#include <boost/interprocess/sync/interprocess_semaphore.hpp>

typedef boost::interprocess::interprocess_semaphore sem;
class Multiplex
{
   private: 
      sem * mutex, *m;
      int n,i;

   public:

      Multiplex(int k) : n(k), mutex(k),i(k),m(1); 
	  {}

      void wait()
      {
	 m->wait();
	 mutex->wait();
	 if(i!=0) i--;
	 m->signal();

      }

      void signal()
      {
	 m->wait();
	 if(i==0) i = n;
	 s->signal();
	 m->signal();
      }

}


class Mutex
{
   private:

      Multiplex * m;

   public:

      Mutex() {	 m = new Multiplex(1); }

      ~Mutex() { delete m; }

      void wait() { m->wait() }

      void signal() { m-> signal() }
}


