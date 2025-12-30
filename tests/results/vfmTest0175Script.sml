Theory vfmTest0175[no_sig_docs]
Ancestors vfmTestDefs0175
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0175";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
