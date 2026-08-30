signature byteStringCacheLib = sig
  include Abbrev
  val cached_bytes_from_hex : string -> term
  val cached_byte_chunks_from_hex : string -> term
  val cached_flat_bytes_from_hex : string -> term
end
