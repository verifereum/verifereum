Theory vfmTest1298[no_sig_docs]
Ancestors vfmTestDefs1298
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1298";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
