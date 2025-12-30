Theory vfmTest0892[no_sig_docs]
Ancestors vfmTestDefs0892
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0892";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
