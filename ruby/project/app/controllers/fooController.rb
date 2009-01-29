class FooController < Mouse::Controller
   def index(*args)
      renderText("args: #{args.inspect}, GET: #{@request.GET.inspect}")
   end
end
