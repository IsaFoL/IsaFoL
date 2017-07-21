(*
  Buffered reader to expose a file of 
  little-endian int32 values as a stream in 
  reverse order, i.e., the last int is read first.
*)
signature BIN_READER = sig
  (* Type of stream *)
  type rd
  (* Exception to be thrown on error *)
  exception Err of string
  (* Open a file *)
  val openf : string -> Position.int * rd
  (* Read a signed 32 bit integer, and return as int *)
  val rd32 : rd -> int * rd
  (* Check if end of stream (beginning of file) has been reached *)
  val at_end : rd -> bool
  
  (* Get position where last int has been read from. At least one int must have been read for this to be accurate! *)
  val last_rd_pos : rd -> Position.int
  
  val buf_size : Position.int ref
end

structure Bin_Reader : BIN_READER = struct
  type rd = { 
    buf_start_pos : Position.int,
    in_buf_pos : int,
    buf : Word8ArraySlice.slice,
    fd : Posix.IO.file_desc
  }

  exception Err of string

  val buf_size = ref (Position.fromInt 65536)
  
  fun openf name = let
    open Posix
    val fd = FileSys.openf(name,FileSys.O_RDONLY,FileSys.O.nonblock) 
    val st = FileSys.fstat fd
    val size = FileSys.ST.size st
    
    val buf_start_pos = if size=0 then 0 else (Position.div (size - 1, !buf_size) + 1) * (!buf_size)
    
    val arr = Word8Array.array(Position.toInt (!buf_size), Word8.fromInt 0)
    val arrsl = Word8ArraySlice.slice(arr,0,NONE)
    
  in
    ( size,
      {
        buf_start_pos = buf_start_pos,
        in_buf_pos = 0,
        buf = arrsl,
        fd=fd
      }
    )
  end

  fun prepare_rd (rd as {buf_start_pos, in_buf_pos, buf, fd}) = 
    if in_buf_pos = 0 then 
      let
        val _ = buf_start_pos >= !buf_size orelse raise Err "Read beyond start of file"
        val buf_start_pos = buf_start_pos - !buf_size
        val xxpos = Posix.IO.lseek (fd,buf_start_pos,Posix.IO.SEEK_SET)
        val _ = xxpos = buf_start_pos orelse raise Err "Invalid seek pos"
        val in_buf_pos = Posix.IO.readArr (fd,buf)
        val _ = in_buf_pos > 0 orelse raise Err "Read 0 bytes?"
      in
        {buf_start_pos = buf_start_pos,in_buf_pos = in_buf_pos, buf = buf, fd = fd}
      end
    else
      rd
  
  fun rd32 rd = let
    val {buf_start_pos, in_buf_pos, buf, fd} = prepare_rd rd
    val _ = in_buf_pos >= 4 orelse raise Err "Unaligned in-buf-pos?"
    val in_buf_pos = in_buf_pos - 4
    val b1 = Word8.toLarge (Word8ArraySlice.sub (buf,in_buf_pos + 0))
    val b2 = Word8.toLarge (Word8ArraySlice.sub (buf,in_buf_pos + 1))
    val b3 = Word8.toLarge (Word8ArraySlice.sub (buf,in_buf_pos + 2))
    val b4 = Word8.toLarge (Word8ArraySlice.sub (buf,in_buf_pos + 3))

    val res = Word32.fromLarge (b1 + LargeWord.<<(b2, Word.fromInt 8) + LargeWord.<<(b3, Word.fromInt 16) + LargeWord.<<(b4, Word.fromInt 24))
    val res = Word32.toIntX res 
    val rd = {buf_start_pos = buf_start_pos,in_buf_pos = in_buf_pos, buf = buf, fd = fd}
  in
    (res, rd)
  end
  
  
  fun at_end {buf_start_pos, in_buf_pos, buf, fd} = buf_start_pos = Position.fromInt 0 andalso in_buf_pos = 0
  
  fun last_rd_pos {buf_start_pos, in_buf_pos, buf, fd} = buf_start_pos + Position.fromInt in_buf_pos
  
  
  
end
