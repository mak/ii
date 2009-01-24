#require 'template'

module ChujWieCo
   class Controller

      def initialize (request, response)
	 p request.class
	 @request,@response = request,response
      end

      def renderText text
	 @response.body << text
      end

      def renderTmpl(path, context={})
	 Template.new(path,context)
      end

      def redirect(location)
      end

      def process(action,args=[])
	 self.__send__(action,*args)
	 @response.finish
      end

   end

   class HTTPError < Controller
      def http404
	 @response.status = 404
	 renderText('<h1>404 Not Found</h1>')
      end

      def http500(exception)
	 @response.status = 500
	 renderText('<h1>500 Internal Server Error</h1>')
	 raise exception
      end
   end
end
