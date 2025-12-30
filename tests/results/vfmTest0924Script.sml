Theory vfmTest0924[no_sig_docs]
Ancestors vfmTestDefs0924
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0924";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
