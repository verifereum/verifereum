Theory vfmTest0462[no_sig_docs]
Ancestors vfmTestDefs0462
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0462";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
