## Routes file, define controllers for application 

routes = %w(
  ^/$
  ^/:index/$
  ^/:world/$	    
  ^/:foo/@id/*$
  ^/:index/ssij/$
  ^/:bar/$
)

## :controller, action, @variable 
