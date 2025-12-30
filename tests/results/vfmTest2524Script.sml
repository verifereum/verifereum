Theory vfmTest2524[no_sig_docs]
Ancestors vfmTestDefs2524
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2524";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
