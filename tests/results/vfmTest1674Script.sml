Theory vfmTest1674[no_sig_docs]
Ancestors vfmTestDefs1674
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1674";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
