Theory vfmTest2056[no_sig_docs]
Ancestors vfmTestDefs2056
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2056";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
