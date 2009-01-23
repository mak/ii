require 'tk'

class SQL

  $db = nil 
  @id = 0
  
  def initialize
     $db = DBI.connect('DBI:SQLite:.addresses.db')
     begin
	@id = $db.select_all('SELECT * FROM Addresses').size
     rescue DBI::DatabaseError => e
	self.create
	@id = $db.select_all('SELECT * FROM Addresses').size
     end
     @id -= 1 if @id != 0 
  end

  def add
    begin
      row = $db.do("INSERT INTO Addresses (id,name,sname,addr,phone,mail,jid) VALUES \
		   (#{@id}, '#{$name.value}', '#{$sname.value}', '#{$addr.value}','#{$phone.value}','#{$mail.value}','#{$jid.value}')")
      if row == 1
	@list.insert @id,[@id,$name.value,$sname.value,$addr.value,$phone.value,$mail.value,$jid.value]
	@id += 1
      end
    rescue DBI::DatabaseError => e
      puts "An error occurred"
      puts "Error code: #{e.err}"
      puts "Error message: #{e.errstr}"
    end
  end


  def del(id)
    begin
       $db.do("DELETE FROM Addresses WHERE id='#{id}'")
       #puts 'Row delted'
    rescue DBI::DatabaseError => e
      puts "An error occurred"
      puts "Error code: #{e.err}"
      puts "Error message: #{e.errstr}"
    end
  end

  def show
    @list.clear
    i=0
    begin
      rows = $db.execute('SELECT * FROM Addresses')
      #puts "ID\tName\tSname\tAddr\tPhone\ttMail\tJID"
      rows.each do |r|
       #puts "#{row[0]}\t#{row[1]}\t#{row[2]}\t#{row[3]}\t#{row[4]}\t#{row[5]}\t#{row[6]}"
       #ret << [r[0],r[1],r[2],r[3],r[4],r[5],r[6]]
       @list.insert i,[r[0],r[1],r[2],r[3],r[4],r[5],r[6]]
       i+=1
      end
      rows.finish   
    rescue DBI::DatabaseError => e
      puts "An error occurred"
      puts "Error code: #{e.err}"
      puts "Error message: #{e.errstr}"
    end
  end

  def find
     begin
       @list.clear
       i =0
       row = $db.execute("SELECT * FROM Addresses WHERE name like '%#{$find.value}%'")
       if row 
	  #puts "ID\tName\tSname\tAddr\tPhone\tMail\tJID"
	  row.each {|r|
	     #puts "#{r[0]}\t#{r[1]}\t#{r[2]}\t#{r[3]}\t#{r[4]}\t#{r[5]}\t#{r[6]}"
	     @list.insert i,[r[0],r[1],r[2],r[3],r[4],r[5],r[6]]
	     i+=1
	  }
       end
    rescue DBI::DatabaseError => e
      puts "An error occurred"
      puts "Error code: #{e.err}"
      puts "Error message: #{e.errstr}"
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

  def fun
     curr = @list.curselection
     id = @list.get(curr).to_i
     self.del(id)
     @list.delete curr
  end

  def gui(c)
    @win = TkRoot.new(){title 'Address Book'}      

    @frame_list = TkLabelframe.new(@win){grid(:row=>1, :column=>0)}
    @frame_list['borderwidth']=1
    @frame_list['relief']='solid'
    
    @frame_entry = TkFrame.new(@win){grid(:row=>2, :column=>0)}
    @frame_entry['borderwidth']=2
    @frame_entry['relief']='sunken'

    @frame_adres = TkLabelframe.new(@frame_entry){text 'Adres';grid(:row=>1, :columnspan=>4, :column=>0)}
    @frame_adres['borderwidth']=1
    @frame_adres['relief']='solid'

    @frame_find = TkLabelframe.new(@win){grid(:row=>3,:column=>0)}
    @frame_find['borderwidth']=0
    @frame_find['relief']='solid'

    @del_button = TkButton.new(@frame_list){grid(:row=>2, :column =>0); text 'Delete';command{c.fun }}
    @quit_button = TkButton.new(@win){grid(:row=>4, :column=>0, :sticky=>'E'); command{exit}; text 'Exit'}
    @add_button = TkButton.new(@frame_entry){text 'Add';grid(:row=>2, :columnspan=>4, :column => 0);command {c.add}}
    @find_button = TkButton.new(@frame_find){text 'Find';grid(:row=>1, :columnspan=>4, :column => 2);command {c.find}}
    @show_button = TkButton.new(@win){grid(:row=>4, :column =>0); text 'Show';command{c.show }}


    @list = TkListbox.new(@frame_list){width '50';grid(:row=>1, :column=>0)}
    @list_label = TkLabel.new(@frame_list){grid(:row=>0,:column=>0); text "Id  Name\t Sname\t Address\t  Phone\t  Mail\t Jid\t\t"}
    self.show


    $name = TkVariable.new
    @name_label =TkLabel.new(@frame_entry){grid(:row=>0,:column=>0); text 'Name:'}
    @name_entry =TkEntry.new(@frame_entry){grid(:row=>0, :column=>1); textvariable $name}

    $sname = TkVariable.new
    @sname_label=TkLabel.new(@frame_entry){grid(:row=>0, :column=>2); text 'Surename:'}
    @sname_entry=TkEntry.new(@frame_entry){grid(:row=>0, :column=>3); textvariable $sname}

    $addr = TkVariable.new
    @addr_label = TkLabel.new(@frame_adres){text 'Address:'; grid(:row=>1, :column=>1)}
    @addr_entry = TkEntry.new(@frame_adres){grid(:row=>1, :column=>2, :columnspan=>3); textvariable $addr}

    $mail = TkVariable.new
    @mail_label = TkLabel.new(@frame_adres){text 'E-mail Adress:'; grid(:row=>2, :column=>1)}
    @mail_entry = TkEntry.new(@frame_adres){grid(:row=>2, :column=>2, :columnspan=>3); textvariable $mail}

    $phone = TkVariable.new
    @phone_label = TkLabel.new(@frame_adres){text 'Phone Adress:'; grid(:row=>3, :column=>1)}
    @phone_entry = TkEntry.new(@frame_adres){grid(:row=>3, :column=>3, :columnspan=>3); textvariable $phone}

    $jid = TkVariable.new
    @jid_label = TkLabel.new(@frame_adres){text 'Jid:'; grid(:row=>4, :column=>1)}
    @jid_entry = TkEntry.new(@frame_adres){grid(:row=>4, :column=>4, :columnspan=>3); textvariable $jid}

    $find = TkVariable.new
    @find_label = TkLabel.new(@frame_find){text 'Find:'; grid(:row=>1, :column=>0)}
    @find_entry = TkEntry.new(@frame_find){grid(:row=>1, :column=>1, :columnspan=>1); textvariable $find}

  
    Tk.mainloop
  end
end

sql = SQL.new
sql.gui sql

