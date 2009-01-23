require 'test/unit'
require 'Lista2'
require 'Lista3'

class TestPath < Test::Unit::TestCase
      @@graf = {'jeden' => ['dwa','trzy'], 'dwa' => ['trzy','cztery'], 
		'trzy' => ['jeden','dwa','cztery'], 'cztery' => ['dwa','trzy']}

      def test_path
	 corr = [["jeden", "dwa", "trzy", "cztery"], ["jeden", "dwa", "cztery"], 
		 ["jeden", "trzy", "dwa", "cztery"], ["jeden", "trzy", "cztery"]]
	 assert_equal(corr,path(@@graf,'jeden','cztery'))
      end
end

class TestSive < Test::Unit::TestCase
   
   def test_sive
      corr = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 
	      43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
      assert_equal(corr,sive(100))
   end
end

class TestFac < Test::Unit::TestCase

   def test_fac
      corr = [[2, 2], [3, 3], [7, 1]]
      assert_equal(corr,factorial(756))
   end
end
