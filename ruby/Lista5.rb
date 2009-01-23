
require 'open-uri'
require 'md5'
require 'yaml'
require 'optparse'
require 'thread'

class Monitor

   @@state = {}
   @@addresses = []
   @@store = true
   @@restore = false
   @@semaphore = Mutex.new

   def initialize(addresses,store = true,restore = false)
      @@store = store
      @@restore = restore
      addresses.each do |a| 
	 @@state[a] = [] if not @@restore
	 @@addresses << a
      end
      self.restoreState if @@restore
   end

   def checkPage(address)
      begin
	page = URI.parse(address).read
      rescue
	 puts 'Error: ' + $!
      end
      checksum = MD5.new(page).hexdigest
      if checksum != @@state[address][0]
	 puts "Page #{address} have been changed" if not @@state[address].empty?
	 @@state[address] = [checksum,page]
      end
      return nil
   end

   def run
      while true
	 _run
	 sleep 10
      end
   end

   def _run
      threads = [] 
      @@addresses.each do |a|
	 threads << Thread.new(a) do |url|
	    self.checkPage url
	    self.storeState if @@store
	 end
      end
      threads.each {|t| t.join}
   end

   def getState
      @@state
   end

   def storeState
       @@semaphore.synchronize {self._storeState}
   end

   def _storeState
      st = @@state.to_yaml
      begin
	 File.open('.state','w') do |l|
	    YAML.dump(@@state , l )
	 end
      rescue
	 puts 'Error: ' + $! + "\n"
	 exit 0
      end
   end

   def restoreState
      begin
	@@state = YAML.load_file( '.state' ) 
      rescue 
	 puts 'Error: ' + $! + "\n"	 
	 exit 0
      end
   end
end

class Run

   @@s = false
   @@r = false
   @@opts = OptionParser.new
   def run
      if parsed?
	 list = $stdin.readline.split(' ')
	 p list
	 Monitor.new(list,@@s,@@r).run
      else
	 usage
      end
   end

   def parsed? 
      @@opts.on('-h','--help') { help }
      @@opts.on('-r','--restore') {@@r = true}
      @@opts.on('-s','--store') {@@s = true }
      @@opts.parse!(ARGV) rescue return false
      return true
   end

   def help
      usage
      puts 'Options'
      puts '  -h, --help	  Displays help message'
      puts '  -s, --store	  Store session after each check'
      puts '  -r, --restore	  Restore session before monitoring'
      exit 0
   end
   
   def usage
      puts "./#{@@opts.program_name}  [-h] [-r] [-s] "
   end
end

Run.new.run
