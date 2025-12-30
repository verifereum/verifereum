Theory vfmTest0142[no_sig_docs]
Ancestors vfmTestDefs0142
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0142";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
