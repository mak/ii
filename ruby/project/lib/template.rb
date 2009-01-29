module Mouse
   class Template
      
      attr_reader :context

      def initialize(file,context={})
	 @context=context
	 @template = init file
      end

      def render(output)
	 output << @template.result(binding)
      end

      def init file
	 input = File.read(file)
	 ERB.new(input,0,"%<>")
      end

      def exec
	 @template.result(binding)
      end

      def include file
	 (init file).result(binding)
      end

   end
end


