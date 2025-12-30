Theory vfmTest2708[no_sig_docs]
Ancestors vfmTestDefs2708
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2708";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
