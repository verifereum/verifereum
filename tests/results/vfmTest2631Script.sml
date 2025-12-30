Theory vfmTest2631[no_sig_docs]
Ancestors vfmTestDefs2631
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2631";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
