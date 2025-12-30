Theory vfmTest2731[no_sig_docs]
Ancestors vfmTestDefs2731
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2731";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
