Theory vfmTest0219[no_sig_docs]
Ancestors vfmTestDefs0219
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0219";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
