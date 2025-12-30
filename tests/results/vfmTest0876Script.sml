Theory vfmTest0876[no_sig_docs]
Ancestors vfmTestDefs0876
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0876";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
