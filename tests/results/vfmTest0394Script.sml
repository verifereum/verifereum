Theory vfmTest0394[no_sig_docs]
Ancestors vfmTestDefs0394
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0394";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
