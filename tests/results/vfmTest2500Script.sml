Theory vfmTest2500[no_sig_docs]
Ancestors vfmTestDefs2500
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2500";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
