Theory vfmTest0158[no_sig_docs]
Ancestors vfmTestDefs0158
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0158";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
