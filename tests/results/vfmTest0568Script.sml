Theory vfmTest0568[no_sig_docs]
Ancestors vfmTestDefs0568
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0568";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
