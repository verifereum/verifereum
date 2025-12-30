Theory vfmTest0127[no_sig_docs]
Ancestors vfmTestDefs0127
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0127";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
