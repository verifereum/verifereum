Theory vfmTest0640[no_sig_docs]
Ancestors vfmTestDefs0640
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0640";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
