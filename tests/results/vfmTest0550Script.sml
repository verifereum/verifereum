Theory vfmTest0550[no_sig_docs]
Ancestors vfmTestDefs0550
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0550";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
