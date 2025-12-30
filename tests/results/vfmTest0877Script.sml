Theory vfmTest0877[no_sig_docs]
Ancestors vfmTestDefs0877
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0877";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
