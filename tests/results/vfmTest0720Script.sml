Theory vfmTest0720[no_sig_docs]
Ancestors vfmTestDefs0720
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0720";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
