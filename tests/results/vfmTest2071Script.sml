Theory vfmTest2071[no_sig_docs]
Ancestors vfmTestDefs2071
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2071";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
