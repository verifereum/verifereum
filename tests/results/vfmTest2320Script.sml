Theory vfmTest2320[no_sig_docs]
Ancestors vfmTestDefs2320
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2320";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
