Theory vfmTest1850[no_sig_docs]
Ancestors vfmTestDefs1850
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1850";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
