Theory vfmTest0713[no_sig_docs]
Ancestors vfmTestDefs0713
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0713";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
