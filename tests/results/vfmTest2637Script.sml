Theory vfmTest2637[no_sig_docs]
Ancestors vfmTestDefs2637
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2637";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
