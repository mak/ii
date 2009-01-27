module Mouse
   class Dispatcher
      
      def initialize(routes,appName)
	 @routes = Mouse::URLResolver.new(routes,appName)
      end

      def call(envoirment)
	 request = Rack::Request.new(envoirment)
	 response = Rack::Response.new
	 @routes.resolve(request,response)
      end
   end
   
   class URLResolver 
      def initialize(routes,appName)	    
	 @routes = routes
	 @appName = appName
	
      end
	 
      def resolve(request,response)
	 p @routes.inspect
	 @routes.each do |regexp |
	    regexp = regexp.gsub(/\*/,'(.*)')
#	    p request.path_info
	    reqPath = request.path_info
#	    p reqPath
#	    p regexp
#	    p @appName
	    reqPath = reqPath + '/' if reqPath[reqPath.size-1..reqPath.size-1] != '/'
	    if md = reqPath.match(regexp)
	       regexp =~ /[a-z0-9]+/
	       if $&
		  action = $&
	       else
		  action = "index"
	       end
#	       p action
	       controller = Object.class_eval("#{@appName}")
	       begin 
		  callable = controller.new(request,response)
		  if callable.respond_to?(action)
		    return callable.process(action, md.captures)
		  else
		    return HTTPError.new(request,response).process(:http404)
		  end
	       rescue => e
		  return HTTPError.new(request, response).process(:http500,e)
	       end
	    end 
	 end   
	 return HTTPError.new(request,response).process(:http404)
      end 
   end 
end

