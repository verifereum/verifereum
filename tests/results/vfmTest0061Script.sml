Theory vfmTest0061[no_sig_docs]
Ancestors vfmTestDefs0061
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0061";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
