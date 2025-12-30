Theory vfmTest0608[no_sig_docs]
Ancestors vfmTestDefs0608
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0608";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
