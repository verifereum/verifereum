Theory vfmTest0495[no_sig_docs]
Ancestors vfmTestDefs0495
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0495";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
