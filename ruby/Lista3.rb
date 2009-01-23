def sive(n)
   sive = (2..n-1).to_a
   sive.map do |p|
      (2..(n/p) +1).map { |y| sive.delete(y*p) }
   end
   return sive
end

def factorial(n)
   tmp = sive(Math.sqrt(n) +2).find_all { |x| n % x == 0 }
   return tmp.map! { |p| [p, ((1..n).find_all {|x| (n % (p ** x)) == 0 }).reverse.first]}
end

