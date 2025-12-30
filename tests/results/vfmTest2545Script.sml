Theory vfmTest2545[no_sig_docs]
Ancestors vfmTestDefs2545
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2545";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
