Theory vfmTest0247[no_sig_docs]
Ancestors vfmTestDefs0247
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0247";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
