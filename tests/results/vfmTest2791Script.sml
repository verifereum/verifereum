Theory vfmTest2791[no_sig_docs]
Ancestors vfmTestDefs2791
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2791";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
