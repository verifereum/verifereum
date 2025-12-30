Theory vfmTest2695[no_sig_docs]
Ancestors vfmTestDefs2695
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2695";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
