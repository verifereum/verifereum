Theory vfmTest0281[no_sig_docs]
Ancestors vfmTestDefs0281
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0281";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
