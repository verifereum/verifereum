Theory vfmTest2381[no_sig_docs]
Ancestors vfmTestDefs2381
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2381";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
