Theory vfmTest0530[no_sig_docs]
Ancestors vfmTestDefs0530
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0530";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
