#include <boost/thread.hpp>
#include <cstdio>
#include <boost/bind.hpp>

#include <boost/interprocess/sync/interprocess_semaphore.hpp>

typedef boost::interprocess::interprocess_semaphore sem;

class Bar 
{
   private:

      int n;
      sem mutex;

      bool knock(void)
      {
	 bool ret;
	 mutex.wait();
	 ret = n < 5 ? ++n || true : false;
	 //printf("knocking, inside: %d\n",n);
	 mutex.post();
	 return ret;
      }

      void leave(void)
      {
	 mutex.wait();
	 n--;
	 printf("leaving, inside: %d\n",n);
	 mutex.post();
      } 

   public:

      Bar() : n(0), mutex(1)
	{}

      void customer(int k)
      {
	 while( !knock());
	 printf("thread %d drinking\n",k);
	 sleep(2);
	 leave();
      }

};

int main(int arc,char **argv)
{
   int k = atoi(argv[1]);
   boost::thread_group tpool; 
   Bar bar;
   for(int i=0;i<k;i++)
   {
      tpool.create_thread(boost::bind(&Bar::customer,&bar,i));
   }
   tpool.join_all();
   return 0;
}

