#!/usr/bin/ruby -w
require 'drb'

def load(x)
   puts  "Load: #{x[0].to_f * 100}% (1 min avg)"
   puts  "Load: #{x[1].to_f * 100}% (5 min avg)"
   puts  "Load: #{x[2].to_f * 100}% (10 min avg)"
   y= x[3].split('/')
   puts  "Procceses: #{y[1]}, running: #{y[0]}"
end



while true
   ['druby://localhost:9000'].each do |a|
      DRb.start_service          
      ps = DRbObject.new(nil,a)          
      load(ps.load)          
      DRb.stop_service
   end     
   sleep 300
end
