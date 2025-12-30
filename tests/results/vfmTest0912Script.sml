Theory vfmTest0912[no_sig_docs]
Ancestors vfmTestDefs0912
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0912";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
