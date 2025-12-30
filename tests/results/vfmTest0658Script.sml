Theory vfmTest0658[no_sig_docs]
Ancestors vfmTestDefs0658
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0658";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
