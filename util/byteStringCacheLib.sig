signature byteStringCacheLib = sig
  include Abbrev
  val cached_bytes_from_hex : string -> term
end
