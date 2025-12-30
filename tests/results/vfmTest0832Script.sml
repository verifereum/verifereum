Theory vfmTest0832[no_sig_docs]
Ancestors vfmTestDefs0832
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0832";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
