Theory vfmTest1288[no_sig_docs]
Ancestors vfmTestDefs1288
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1288";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
