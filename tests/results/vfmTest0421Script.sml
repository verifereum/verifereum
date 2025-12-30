Theory vfmTest0421[no_sig_docs]
Ancestors vfmTestDefs0421
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0421";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
