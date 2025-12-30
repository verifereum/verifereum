Theory vfmTest1032[no_sig_docs]
Ancestors vfmTestDefs1032
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1032";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
