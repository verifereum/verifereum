Theory vfmTest2767[no_sig_docs]
Ancestors vfmTestDefs2767
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2767";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
