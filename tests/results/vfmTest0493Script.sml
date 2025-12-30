Theory vfmTest0493[no_sig_docs]
Ancestors vfmTestDefs0493
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0493";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
