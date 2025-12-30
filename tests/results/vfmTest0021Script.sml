Theory vfmTest0021[no_sig_docs]
Ancestors vfmTestDefs0021
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0021";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
