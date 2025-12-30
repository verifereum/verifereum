Theory vfmTest0673[no_sig_docs]
Ancestors vfmTestDefs0673
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0673";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
