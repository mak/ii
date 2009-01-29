class IndexController < Mouse::Controller
   def index
      render :text => 'Index'
   end

   def ssij
      render :file => 'ssij'
   end
end
