Theory vfmTest0415[no_sig_docs]
Ancestors vfmTestDefs0415
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0415";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
