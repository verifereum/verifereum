Theory vfmTest2574[no_sig_docs]
Ancestors vfmTestDefs2574
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2574";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
