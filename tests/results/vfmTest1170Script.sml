Theory vfmTest1170[no_sig_docs]
Ancestors vfmTestDefs1170
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1170";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
