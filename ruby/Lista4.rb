module Debugger
   def snapshot
      puts "Stan obiektu klasy #{self.class}"
      for iv in self.instance_variables
	 puts "#{iv} = #{self.instance_variable_get(iv)}"
      end
   end

   def check
      puts 'Testing...'
      m = self.methods.find_all {|x| x =~ /^test_*/ }
      m.each do |x|
	 puts "\tPerforming #{self.class}.#{x} : #{
	      eval  'self.' + x}"
      end
   end
end

class Device
   attr_writer :name

   def initialize(name, type)
      @name = name
      @type = type
   end

   def to_s
      @name + ' ' + @type
   end
   
   def name
      @name
   end


   def long_name
      @type + '--->' + @name
   end

   def test_cos
      "test"
   end

   def test_cos_innego
      "test2"
   end

   def nie_test
      "zle"
   end
end


class Printer < Device
   include Debugger
   def initialize(name, type, port)
      super(name, type)
      @port = port
   end
   def to_s
      super.to_s + ''#{@port}''
   end
end

lokalna = Printer.new('kuchenna', 'hp5000N', '/dev/')
lokalna.snapshot
lokalna.check

