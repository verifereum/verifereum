Theory vfmTest2609[no_sig_docs]
Ancestors vfmTestDefs2609
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2609";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
