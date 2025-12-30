Theory vfmTest2721[no_sig_docs]
Ancestors vfmTestDefs2721
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2721";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
