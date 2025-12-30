Theory vfmTest0360[no_sig_docs]
Ancestors vfmTestDefs0360
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0360";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
