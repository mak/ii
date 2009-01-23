require 'dbi'

class SQL

  $db = nil 
  @id = 0
  
  def initialize
     $db = DBI.connect('DBI:SQLite:.addresses.db')
     @id = 0
  end

  def add
    puts 'Name: '
    name = gets.chomp
    puts 'Surname: '
    sname = gets.chomp
    puts 'Address: '
    address = gets.chomp
    puts 'Phone: '
    phone = gets.chomp
    puts 'E-mail :'
    mail = gets.chomp
    puts 'JID: '
    jid = gets.chomp
  
    begin
      row = $db.do("INSERT INTO Addresses (id,name,sname,addr,phone,mail,jid) VALUES \
		   (#{@id}, '#{name}', '#{sname}', '#{address}','#{phone}','#{mail}','#{jid}')")
      if row == 1
	puts 'Row saved'
	@id += 1
      end
    rescue DBI::DatabaseError => e
      puts "An error occurred"
      puts "Error code: #{e.err}"
      puts "Error message: #{e.errstr}"
    end
  end


  def del
    puts 'Insert id row wich should be deleted'
    id = gets.chop
    begin
       $db.do("DELETE FROM Addresses WHERE id='#{id}'")
       puts 'Row delted'
    rescue DBI::DatabaseError => e
      puts "An error occurred"
      puts "Error code: #{e.err}"
      puts "Error message: #{e.errstr}"
    end
  end

  def show
    begin
    rows = $db.execute('SELECT * FROM Addresses')
    puts "ID\tName\tSname\tAddr\tPhone\ttMail\tJID"
    rows.each do |row|
       puts "#{row[0]}\t#{row[1]}\t#{row[2]}\t#{row[3]}\t#{row[4]}\t#{row[5]}\t#{row[6]}"
    end
    rows.finish   
    rescue DBI::DatabaseError => e
      puts "An error occurred"
      puts "Error code: #{e.err}"
      puts "Error message: #{e.errstr}"
    end
  end

  def find
    puts 'Name: '
    name = gets.chomp
    begin
       row = $db.execute("SELECT * FROM Addresses WHERE name like '%#{name}%'")
       if row 
	  puts "ID\tName\tSname\tAddr\tPhone\tMail\tJID"
	  row.each {|r|
	     puts "#{r[0]}\t#{r[1]}\t#{r[2]}\t#{r[3]}\t#{r[4]}\t#{r[5]}\t#{r[6]}"
	  }
       end
    rescue DBI::DatabaseError => e
      puts "An error occurred"
      puts "Error code: #{e.err}"
      puts "Error message: #{e.errstr}"
    end
  end


  def run
    e = 1
    puts 'add  --> insert entry to database'
    puts 'del  --> delete entry from database'
    puts 'show --> show entreis for database'
    puts 'find --> find entreis by name in database'
    while e!=0
	cmd = gets.chop
	if cmd == "exit" then e=0
	else
	   begin
	      method(cmd).call
	   rescue
              puts 'Unknow method'
	   end
	end
    end
  end

  def create
    begin
    r = $db.do('CREATE TABLE Addresses (id int, name text, sname text, addr text ,phone int, mail text, jid text)')
    rescue DBI::DatabaseError => e
      puts "An error occurred"
      puts "Error code: #{e.err}"
      puts "Error message: #{e.errstr}"
    end
  end

end


#sql = SQL.new
#sql.create if not File.exist?('.addresses.db')
#sql.run


