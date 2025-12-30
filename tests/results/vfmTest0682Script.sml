Theory vfmTest0682[no_sig_docs]
Ancestors vfmTestDefs0682
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0682";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
