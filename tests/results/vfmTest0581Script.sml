Theory vfmTest0581[no_sig_docs]
Ancestors vfmTestDefs0581
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0581";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
