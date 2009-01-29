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
	    reqPath = request.path_info
	    reqPath = reqPath + '/' if reqPath[reqPath.size-1..reqPath.size-1] != '/'

	    if md = reqPath.match(regexp.sub(/:/,''))
	       regexp =~ /:(\w)+/
	       ctrlName = $&[1..$&.size]
	       regexp =~ /\/(\w)+/
	       if $&
		  action = $&[1..$&.size]
	       else
		  action = "index"
	       end
	       p action

	       if ctrlName == ''
		  ctrlName = 'indexController'
	       else
		  ctrlName = ctrlName + 'Controller'
	       end

	       require 'controllers/' + ctrlName + '.rb' #laizy class loading?

	       #p ctrlName
	       controller = Object.class_eval("#{Mouse::Helpers.new(ctrlName).fstUpper}")
	       begin 
		  callable = controller.new(request,response)
		  if callable.respond_to?(action)
		    return callable.process(action, md.captures)
    		  else
		    return callable.process(:defResponse)
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

