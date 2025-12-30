Theory vfmTest0850[no_sig_docs]
Ancestors vfmTestDefs0850
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0850";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
