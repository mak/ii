#Maciej Kotowicz 209150
#Lista 1 


#zadanie 1 
def ackerman(n,m)
   if n == 0
      m+1
   elsif m == 0
      ackerman(n-1,1)
   else
      ackerman(n-1,ackerman(n,m-1))
   end
end


def ackTests()
  (0..4).each {|x| (0..4).each {|y| puts "(%d,%d) : %d\n" % [ x,y,ackerman(x,y)]}}
end

#zadanie 3

def sum_(l)
  s =0
  l.each do |x|
     s += x 
  end
  return s
end

def sum(l)
   sum_(l.map {|x| sum_(x) } )
end
   

def sumTests()
  7.times do 
     x = rand(5) + 2
     arr = Array.new(x).map!do 
	y=rand(5) +2
	Array.new(y).map!{rand(20)}
     end
     wyn = sum(arr)
     puts "sum([#{arr.map!{ |w| '['+ w.join(',') +']'}}]) = #{wyn}"
  end
end

#zadanie 5

def skalar(t1,t2)
   ret = 0
   (0..t1.length-1).each do |i|
      ret += t1[i] * t2[i]
   end
   return ret
end

def skalarTests()
   7.times do
      x = rand(5) + 2
      a = Array.new(2).map!{ Array.new(x).map! {rand(30)}}
      wyn = skalar(a[0],a[1])
      puts "f([#{a[0].join(',')+'],['+a[1].join(',')}]) = #{wyn}"
   end
end
#zadanie 6

def slownie(n)
   slownik,ret = {1 => 'jeden', 2 => 'dwa',	  3 => 'trzy',	4 => 'cztery',
	      5 => 'piec',  6 => 'szesc', 7 => 'siedem',8 => 'osiem',
	      9 => 'dziewiec', 0 => 'zero'},""
   n.to_s.split('').each {|x|ret += slownik[x.to_i] + ' '}
   return ret
end

def slownieTests()
   7.times { x = rand(100000 ); puts "slownie(#{x}) = #{slownie(x)}"}
end

#tests

puts 'sum function tests'
sumTests()
puts 'skalar function tests'
skalarTests()
puts 'slownie function tests'
slownieTests()
puts 'Ackerman function tests'
ackTests()

