Theory vfmTest0249[no_sig_docs]
Ancestors vfmTestDefs0249
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0249";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
