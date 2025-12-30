Theory vfmTest1463[no_sig_docs]
Ancestors vfmTestDefs1463
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1463";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
