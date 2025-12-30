Theory vfmTest2606[no_sig_docs]
Ancestors vfmTestDefs2606
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2606";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
