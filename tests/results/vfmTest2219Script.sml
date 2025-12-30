Theory vfmTest2219[no_sig_docs]
Ancestors vfmTestDefs2219
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2219";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
