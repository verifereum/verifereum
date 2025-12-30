Theory vfmTest0202[no_sig_docs]
Ancestors vfmTestDefs0202
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0202";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
