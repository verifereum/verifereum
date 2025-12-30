Theory vfmTest0026[no_sig_docs]
Ancestors vfmTestDefs0026
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0026";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
