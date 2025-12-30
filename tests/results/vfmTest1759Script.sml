Theory vfmTest1759[no_sig_docs]
Ancestors vfmTestDefs1759
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1759";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
