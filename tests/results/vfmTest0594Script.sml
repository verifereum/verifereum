Theory vfmTest0594[no_sig_docs]
Ancestors vfmTestDefs0594
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0594";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
