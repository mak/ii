$: << '../lib'

%w(rack erb controller dispatcher tmpdir).map! {|lib| require lib }

module Mouse 
   class Main
      def initialize
      	 
	 routes = eval(File.read('routes.rb'))
	 appName = Dir.getwd.gsub(/\/(.*)\//,'')
	 
	 require appName

	 appName = fstUpper appName
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

      def fstUpper str
	 str[0..0].upcase + str[1..str.size]
      end
   end
end


Mouse::Main.new
