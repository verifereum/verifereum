signature vfmTestLib = sig
  val mk_prove_test : string -> int * (int -> Thm.thm)
end
