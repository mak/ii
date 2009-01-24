require 'erb'

module ChujWieCo
   class Template
      
      def initialize(path,context)
	 @context=context
	 input = File.read(path)
	 @template = ERB.new(input)
      end

      def render(output)
	 output << @template.evaluate(@context)
      end
   end
end


