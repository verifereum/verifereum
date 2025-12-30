Theory vfmTest0474[no_sig_docs]
Ancestors vfmTestDefs0474
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0474";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
