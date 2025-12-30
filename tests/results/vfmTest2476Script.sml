Theory vfmTest2476[no_sig_docs]
Ancestors vfmTestDefs2476
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2476";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
