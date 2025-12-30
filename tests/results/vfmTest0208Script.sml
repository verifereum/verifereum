Theory vfmTest0208[no_sig_docs]
Ancestors vfmTestDefs0208
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0208";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
