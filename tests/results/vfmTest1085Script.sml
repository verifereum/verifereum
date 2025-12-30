Theory vfmTest1085[no_sig_docs]
Ancestors vfmTestDefs1085
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1085";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
