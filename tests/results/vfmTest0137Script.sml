Theory vfmTest0137[no_sig_docs]
Ancestors vfmTestDefs0137
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0137";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
