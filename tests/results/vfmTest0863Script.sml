Theory vfmTest0863[no_sig_docs]
Ancestors vfmTestDefs0863
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0863";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
