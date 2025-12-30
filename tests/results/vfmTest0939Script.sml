Theory vfmTest0939[no_sig_docs]
Ancestors vfmTestDefs0939
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0939";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
