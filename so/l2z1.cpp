#include <boost/thread.hpp>
#include <cstdio>
#include <cstdlib>
#include <boost/bind.hpp>

#include <boost/interprocess/sync/interprocess_semaphore.hpp>

typedef boost::interprocess::interprocess_semaphore sem;

class CPlace // Conspiracy Place
{

   private:

      int n;
      sem noConspiracy,noPolice,posiblePolice,mutex;
      //std::vector<thread::id> activeConspiracy for disperseConspiracy() witch killing all thread in room
      
      void conspiracyEnter()
      {
	 noPolice.wait();
	 mutex.wait();
	 n++;
	 if(n==1)
	 {
	    possiblePolice.wait();
	    noStudents.wait();
	 }
	 if(n == 44) 
	    possiblePolice.post();
	 mutex.post();
	 noPolice.post();

      }

      void conspiracyLeave()
      {
	 mutex.wait();
	 n--;
	 if(n==0) 
	 {
	    noConspiracy.post();
	    possiblePolice.post();
	 }
	 if(n == 43)
	    possiblePolice.wait();
	 mutex.post();

      }

      void disperseConspiracy()
      {

      }

      void search()
      {

      }

      void doConspiracy()
      {

      }

   public:

      CPlace() : n(0), noConspiracy(1),noPolice(1),possiblePolice(1),mutex(1)
	 {}


      void police()
      {
	 possiblePolice.wait();
	 possiblePolice.post();

	 noPolice.wait();
	 mutex.wait();
	 if(n==0)
	 {
	    search();
	    mutex.post();
	 }
	 if(n >= 44)
	 {
	    disperseConspiracy();
	    mutex.post();
	    noConspiracy.wait();
	    noConspiracy.signal();
	 }
	 else
	    mutex.signal();
	  
	 noPolice.post();
      }

      void conspiracy()
      {
	 conspiracyEnter();
	 doConspiracy();
	 conspiracyLeave();

      }

   }

}

