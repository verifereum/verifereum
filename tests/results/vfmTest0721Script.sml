Theory vfmTest0721[no_sig_docs]
Ancestors vfmTestDefs0721
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0721";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
