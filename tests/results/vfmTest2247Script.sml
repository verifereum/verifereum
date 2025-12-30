Theory vfmTest2247[no_sig_docs]
Ancestors vfmTestDefs2247
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2247";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
