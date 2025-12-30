Theory vfmTest0124[no_sig_docs]
Ancestors vfmTestDefs0124
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0124";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
