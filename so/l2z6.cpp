#include <boost/thread.hpp>
#include <cstdio>
#include <cstdlib>
#include <boost/bind.hpp>

#include <boost/interprocess/sync/interprocess_semaphore.hpp>

typedef boost::interprocess::interprocess_semaphore sem;

class Toilet
{
   private:

      enum gender {MALE, FEMALE,ANY };
      int m,k;
      gender g;
      sem mk,mm,mutex;


      bool knock_male(void)
      {
	 bool ret;
	 mutex.wait();
	 if(g  == MALE || g == ANY )
	 {
	    g = MALE;
	    mutex.post();
	    mm.wait();
	    ret = m < 3 ? ++m || true : false;
	    //printf("knocking, inside: %d\n",n);
	    mm.post();
	    return ret;
	 }
	 mutex.post();
	 return false;
      }
      bool knock_female(void)
      {
	 bool ret;
	 mutex.wait();
	 if(g  == FEMALE || g == ANY )
	 {
	    g = FEMALE;
	    mutex.post();
	    mk.wait();
	    ret = k < 3 ? ++k || true : false;
	    //printf("knocking, inside: %d\n",n);
	    mk.post();
	    return ret;
	 }
	 mutex.post();
	 return false;
      }

      void leave_male(void)
      {
	 mm.wait();
	 m--;
	 mutex.wait();
	 if(m==0) g = ANY;
	 mutex.post(); 
	 printf("leaving, inside: %d\n",m);
	 mm.post();	
      } 
      void leave_female(void)
      {
	 mk.wait();
	 k--;
	 mutex.wait();
	 if(k==0) g = ANY;
	 mutex.post(); 
	 printf("leaving, inside: %d\n",k);
	 mk.post();	
      } 

   public:

      Toilet() : m(0), k(0),mk(1),mm(1), mutex(1) { g = ANY; }
      void customer_male(int k)
      {
	 printf("male thread %d waiting \n",k);
	 while( !knock_male());
	 printf("thread %d in toilet \n",k);
	 sleep(rand() % 3 );
	 leave_male();
      }

      void customer_female(int k)
      {
	 printf("female thread %d waiting \n",k);
	 while( !knock_female());
	 printf("thread %d in toilet \n",k);
    	 sleep(rand() % 4 );
	 leave_female();
      }


};

int main(int arc,char **argv)
{
   int k = atoi(argv[1]);
   boost::thread_group tpool; 
   Toilet toilet;
   srand(time(NULL));
   for(int i=0;i<k;i++)
   {
      int r = rand() %2 ;
      printf("gender: %s\n",r == 0 ? "MALE" : "FEMALE");
      if (r == 0 ) 
	 tpool.create_thread(boost::bind(&Toilet::customer_male,&toilet,i));
      else
	 tpool.create_thread(boost::bind(&Toilet::customer_female,&toilet,i));

   }
   tpool.join_all();
   return 0;
}

