Theory vfmTest0746[no_sig_docs]
Ancestors vfmTestDefs0746
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0746";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
