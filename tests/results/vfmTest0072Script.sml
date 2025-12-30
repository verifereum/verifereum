Theory vfmTest0072[no_sig_docs]
Ancestors vfmTestDefs0072
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0072";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
