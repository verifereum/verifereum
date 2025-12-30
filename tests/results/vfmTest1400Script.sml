Theory vfmTest1400[no_sig_docs]
Ancestors vfmTestDefs1400
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1400";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
