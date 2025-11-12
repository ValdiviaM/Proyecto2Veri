//Se extiende de la clase base
class router_sequence_item extends uvm_sequence_item;

//formato de los campos de los paquetes del s_routing_table
bit [7:0]term_or_dir;//(terminal / direction / broadcast)
bit [3:0] dst_row;   //(destination row)
bit [3:0] dst_col;  //(destination column)
bit      mode;     //routing mode: row-first vs column-first)
bit [7:0] src;      //(source ID)
bit [7:0] id;      //(packet ID / sequence number)
bit [6:0] payload; //payload

//Provide pack() to create a [pck_sz-1:0] vector and unpack() to decode from the wires.

// build phase (constructor)
function new (string name = "packets");
	super.new(name);
endfunction : new


endclass:router_sequence_item 
