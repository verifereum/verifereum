Theory vfmTest0411[no_sig_docs]
Ancestors vfmTestDefs0411
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0411";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
