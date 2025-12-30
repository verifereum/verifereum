Theory vfmTest2133[no_sig_docs]
Ancestors vfmTestDefs2133
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2133";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
