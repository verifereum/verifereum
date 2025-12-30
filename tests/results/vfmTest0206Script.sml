Theory vfmTest0206[no_sig_docs]
Ancestors vfmTestDefs0206
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0206";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
