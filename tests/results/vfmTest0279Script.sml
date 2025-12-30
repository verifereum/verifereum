Theory vfmTest0279[no_sig_docs]
Ancestors vfmTestDefs0279
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0279";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
