Theory vfmTest2664[no_sig_docs]
Ancestors vfmTestDefs2664
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2664";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
