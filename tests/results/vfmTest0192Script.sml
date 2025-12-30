Theory vfmTest0192[no_sig_docs]
Ancestors vfmTestDefs0192
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0192";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
