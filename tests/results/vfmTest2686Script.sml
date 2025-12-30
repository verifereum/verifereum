Theory vfmTest2686[no_sig_docs]
Ancestors vfmTestDefs2686
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2686";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
