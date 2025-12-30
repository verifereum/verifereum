Theory vfmTest0264[no_sig_docs]
Ancestors vfmTestDefs0264
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0264";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
