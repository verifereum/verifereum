Theory vfmTest2603[no_sig_docs]
Ancestors vfmTestDefs2603
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2603";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
