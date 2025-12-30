Theory vfmTest0830[no_sig_docs]
Ancestors vfmTestDefs0830
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0830";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
