($: << '../lib') << './lib'

%w(rack erb template controller dispatcher tmpdir helpers).map! {|lib| require lib }

module Mouse 
   class Main
      def initialize
      	 
	 routes = eval(File.read('routes.rb'))
	 appName = Dir.getwd.gsub(/\/(.*)\//,'')
	 
	 #require appName no longer needed?

	 #appName = fstUpper appName
	 #loadContrllers
	 app = Rack::Builder.new {
	    use Rack::CommonLogger, STDERR
	    use Rack::ShowExceptions
	    use Rack::Reloader
	    use Rack::Lint
	    use Rack::Static , :urls => ['/img', '/css', '/js'], :root => './'
	    run Mouse::Dispatcher.new(routes,appName)
	 }.to_app
	 
	 Rack::Handler::Mongrel.run(app,{:Host => 'localhost', :Port => 8080})
      end

   end
end


Mouse::Main.new
