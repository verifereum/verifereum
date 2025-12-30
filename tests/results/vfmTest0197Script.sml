Theory vfmTest0197[no_sig_docs]
Ancestors vfmTestDefs0197
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0197";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
