Theory vfmTest2677[no_sig_docs]
Ancestors vfmTestDefs2677
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2677";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
