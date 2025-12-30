Theory vfmTest0147[no_sig_docs]
Ancestors vfmTestDefs0147
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0147";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
