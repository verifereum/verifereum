Theory vfmTest2429[no_sig_docs]
Ancestors vfmTestDefs2429
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2429";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
