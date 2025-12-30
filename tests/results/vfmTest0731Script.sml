Theory vfmTest0731[no_sig_docs]
Ancestors vfmTestDefs0731
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0731";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
