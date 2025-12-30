Theory vfmTest1166[no_sig_docs]
Ancestors vfmTestDefs1166
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1166";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
