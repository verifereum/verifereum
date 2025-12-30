Theory vfmTest0506[no_sig_docs]
Ancestors vfmTestDefs0506
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0506";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
