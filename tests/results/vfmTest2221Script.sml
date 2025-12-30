Theory vfmTest2221[no_sig_docs]
Ancestors vfmTestDefs2221
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2221";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
