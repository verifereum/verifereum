Theory vfmTest0945[no_sig_docs]
Ancestors vfmTestDefs0945
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0945";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
