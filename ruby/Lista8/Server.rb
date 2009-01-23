#!/usr/bin/ruby -w
require 'drb'

class DistMonit
   def load
      File.open('/proc/loadavg','r').readline.split(' ')
   end
end

DRb.start_service('druby://localhost:9000',DistMonit.new)
puts DRb.uri

DRb.thread.join

