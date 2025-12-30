Theory vfmTest1264[no_sig_docs]
Ancestors vfmTestDefs1264
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1264";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
