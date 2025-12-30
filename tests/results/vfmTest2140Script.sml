Theory vfmTest2140[no_sig_docs]
Ancestors vfmTestDefs2140
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2140";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
