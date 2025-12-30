Theory vfmTest2093[no_sig_docs]
Ancestors vfmTestDefs2093
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2093";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
