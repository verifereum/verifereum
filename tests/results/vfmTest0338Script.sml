Theory vfmTest0338[no_sig_docs]
Ancestors vfmTestDefs0338
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0338";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
