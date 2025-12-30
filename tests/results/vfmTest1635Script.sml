Theory vfmTest1635[no_sig_docs]
Ancestors vfmTestDefs1635
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1635";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
