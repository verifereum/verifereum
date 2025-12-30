Theory vfmTest0161[no_sig_docs]
Ancestors vfmTestDefs0161
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0161";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
