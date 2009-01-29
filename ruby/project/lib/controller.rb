module Mouse
   class Controller 

      def initialize (request, response)
	 @request,@response = request,response
      end

      def render args
	 #p self.to_s
	 if args[:text]
	    renderText args[:text]
	 else
	    viewName = Mouse::Helpers.new(self.class.to_s.gsub(/Controller/,'')).fstLower
	    renderTmpl('views/'+ viewName + '/lay.erb',args)
	  end
      end

      def redirect(location)
      end

      def process(action,args=[])
	 self.__send__(action,*args)
	 @response.finish
      end
 
      private 
      
      def renderText text
         @response.body << text
      end

      def renderTmpl(path, context={})
         Template.new(path,context).render(@response.body)
      end


      def defResponse
	 begin
	    viewName = Mouse::Helpers.new(self.class.to_s.gsub(/Controller/,'')).fstLower
	    tmpl = Template.new('views/' + viewName + '/lay.erb',{})
	    tmpl.render(@response.body)
	 rescue Errno::ENOENT => e
	    renderText '<h1>404 Not Found </h1>'
	 end
      end


   end

   class HTTPError < Controller
      def http404
	 @response.status = 404
	 render :text => '<h1>404 Not Found</h1>'
      end

      def http500(exception)
	 @response.status = 500
	 render :text => '<h1>500 Internal Server Error</h1>'
	 raise exception
      end
   end
end
