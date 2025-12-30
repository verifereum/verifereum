Theory vfmTest2057[no_sig_docs]
Ancestors vfmTestDefs2057
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2057";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
