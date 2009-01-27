class App < Mouse::Controller
   def index
      renderText('Index')
   end

   def world
      renderText('Hello World')
   end

   def foo(*args)
      renderText("args: #{args.inspect}, GET: #{@request.GET.inspect}")
   end

   def bar
   end
end

