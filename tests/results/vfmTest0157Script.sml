Theory vfmTest0157[no_sig_docs]
Ancestors vfmTestDefs0157
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0157";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
