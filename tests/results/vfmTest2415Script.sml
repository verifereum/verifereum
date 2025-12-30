Theory vfmTest2415[no_sig_docs]
Ancestors vfmTestDefs2415
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2415";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
