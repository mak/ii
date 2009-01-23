def path(g,a,b,acc = [a])
   g[a].inject [] do |paths,e|
      if acc.any? { |x| x == e }
	 paths
      elsif e == b
	 paths + [ acc + [e] ]
      elsif not (newpath = path(g,e,b,acc + [e])).empty?
	 paths + newpath
      else
	 paths
      end
   end
end

