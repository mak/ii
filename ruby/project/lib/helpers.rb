module Mouse
   class Helpers

      def initialize str
	 @str = str
      end

      def fstUpper
	 @str[0..0].upcase + @str[1..@str.size]
      end

      def fstLower
	 @str[0..0].downcase + @str[1..@str.size]
      end
   end
end

