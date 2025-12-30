Theory vfmTest2383[no_sig_docs]
Ancestors vfmTestDefs2383
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2383";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
